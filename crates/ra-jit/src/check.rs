//! `ra-jit --check <project> …`: the daemon's `cargo ra-jit check` of a build it has no
//! programs of. It loads the workspace as the worker of that build does and builds nothing:
//! each request on its socket is answered with what rust-analyzer finds in the crates of the
//! workspace, as a build says its errors. No rustc checks the source.

use std::{
    path::{Path, PathBuf},
    time::SystemTime,
};

use anyhow::Context as _;
use ide_db::{
    ChangeWithProcMacros, RootDatabase,
    base_db::{SourceDatabase as _, TargetKind},
};
use project_model::ProjectWorkspaceKind;
use rustc_hash::{FxHashMap, FxHashSet};
use vfs::Vfs;

use crate::{Args, Parts, Sources, Watched, WatchedFile};

/// What a checker answers when the workspace changed in a way only loading it again takes
/// in: a source file came or went, a manifest changed, or the source of a build script or a
/// proc macro did, which run as they were built.
pub(crate) const RELOAD: &str = "reload";

/// What a lint request starts with, before its [`blaze_lints::serve::Ask`]; its answer starts
/// with it too, before the [`blaze_lints::serve::Answer`].
pub(crate) const LINT: &str = "lint\t";

/// Loads the workspace of `args` and answers the check requests on its socket.
pub(crate) fn serve(args: Args) -> anyhow::Result<()> {
    let socket = args.socket.clone().context("--check needs --socket")?;
    crate::process_wide();
    let read_from = SystemTime::now();
    let cargo_config = crate::cargo_config(&args);
    let projects = [args.project.as_path()];
    let selection = args.selection.clone();
    let (mut db, vfs, checkouts) =
        crate::load(&projects, &cargo_config, crate::load_config(), selection, None, None)?;
    ide_db::base_db::set_process_env(&mut db, crate::process::own());
    let Parts { root, members, lints_capped, .. } = checkouts.parts(&args.project)?;
    let mut checker = Checker::new(
        &db,
        &vfs,
        &checkouts,
        &members,
        &args.selection,
        read_from,
        root,
        lints_capped,
    );
    let served = match crate::socket::Served::bind(&socket) {
        Ok(served) => served,
        Err(crate::socket::NotServed::Taken) => {
            anyhow::bail!("another checker serves {}", socket.display())
        }
        Err(crate::socket::NotServed::Failed(error)) => {
            anyhow::bail!("listening on {}: {error}", socket.display())
        }
    };
    eprintln!("checking {} files of {} crates", checker.checked.len(), checker.crates);
    for (stream, _open) in served.incoming() {
        let Ok(request) = crate::socket::read_request(&stream) else {
            continue;
        };
        let reply = match checker.refresh(&mut db) {
            Some(reload) => {
                eprintln!("{RELOAD}: {reload}");
                RELOAD.to_owned()
            }
            None => match (checker.verdict(&db), request.strip_prefix(LINT)) {
                (verdict, Some(ask)) if verdict == "ok" => checker.lints(&db, ask),
                (verdict, _) => verdict,
            },
        };
        let _ = std::io::Write::write_all(&mut &stream, format!("{reply}\n").as_bytes());
        if reply == RELOAD {
            break;
        }
    }
    Ok(())
}

/// The verdict of a `cargo blaze check` on the crates of `project`, `krate` among them, once,
/// as a build script's probe of rustc is answered (`as_rustc.rs`): `None` when they compile,
/// else their errors.
pub(crate) fn once(project: &Path, krate: &str) -> anyhow::Result<Option<crate::Refused>> {
    let project = project.to_str().context("a path that is not text")?.to_owned();
    // A build's arguments, of which a check reads the project and the crate.
    let out = std::env::temp_dir().join("unwritten.o").to_string_lossy().into_owned();
    let args = [project, "--crate".to_owned(), krate.to_owned(), "--out".to_owned(), out];
    let args = Args::parse(args.into_iter())?;
    crate::process_wide();
    let read_from = SystemTime::now();
    let cargo_config = crate::cargo_config(&args);
    let projects = [args.project.as_path()];
    let (mut db, vfs, checkouts) = crate::load(
        &projects,
        &cargo_config,
        crate::load_config(),
        args.selection.clone(),
        None,
        None,
    )?;
    ide_db::base_db::set_process_env(&mut db, crate::process::own());
    let Parts { root, members, lints_capped, .. } = checkouts.parts(&args.project)?;
    let checker = Checker::new(
        &db,
        &vfs,
        &checkouts,
        &members,
        &args.selection,
        read_from,
        root,
        lints_capped,
    );
    if let Some(refused) = checker.refused(&db) {
        return Ok(Some(refused));
    }
    Ok(checker.checked.iter().find_map(|&file| unresolved(&db, file)).map(|path| {
        crate::Refused::Error(crate::errors::Said::one(crate::errors::Diagnostic {
            code: Some("E0433".to_owned()),
            message: format!("failed to resolve `{path}`"),
            span: None,
        }))
    }))
}

/// A path of the file, outside its attributes, that names nothing: rustc's E0433, which
/// rust-analyzer does not say of a type's path, and on which a probe of a library item
/// turns (autocfg's `probe_trait("alloc::alloc::Allocator")` with no `extern crate alloc`).
fn unresolved(db: &RootDatabase, file: vfs::FileId) -> Option<String> {
    use syntax::{AstNode as _, ast};
    let sema = hir::Semantics::new(db);
    let tree = sema.parse_guess_edition(file);
    tree.syntax().descendants().filter_map(ast::Path::cast).find_map(|path| {
        let in_attr = path.syntax().ancestors().any(|it| ast::Attr::can_cast(it.kind()));
        (!in_attr && sema.resolve_path(&path).is_none()).then(|| path.to_string())
    })
}

struct Checker {
    /// The source files of the workspace as they were last read.
    files: Vec<WatchedFile>,
    /// The files of the crates checked, which are the workspace's.
    checked: Vec<vfs::FileId>,
    crates: usize,
    /// The files of the build scripts and proc macros of the workspace.
    ran: FxHashSet<vfs::FileId>,
    /// Where new source files of the crates checked would be.
    dirs: Vec<PathBuf>,
    /// Every file loaded, by path.
    loaded: FxHashSet<PathBuf>,
    /// The manifests, the lock file and cargo's configuration, as they were when loaded.
    manifests: FxHashMap<PathBuf, Option<SystemTime>>,
    sources: Sources,
    root: PathBuf,
    lints_capped: bool,
    /// The crates `cargo blaze clippy` lints: the workspace's, proc macros included, build
    /// scripts not.
    linted: Vec<ide_db::base_db::Crate>,
    /// Where each file loaded is, for naming them in lints.
    located: FxHashMap<vfs::FileId, PathBuf>,
}

impl Checker {
    #[expect(clippy::too_many_arguments)]
    fn new(
        db: &RootDatabase,
        vfs: &Vfs,
        checkouts: &crate::Checkouts,
        members: &FxHashSet<ide_db::base_db::Crate>,
        selection: &crate::plan::Selection,
        read_from: SystemTime,
        root: PathBuf,
        lints_capped: bool,
    ) -> Checker {
        let files = WatchedFile::sources(vfs, db, read_from);
        let paths: FxHashMap<_, _> = files
            .iter()
            .filter_map(|it| match it.file {
                Watched::Source(id) => Some((id, it.path.clone())),
                Watched::Included(_) => None,
            })
            .collect();
        let mut ran_roots = FxHashSet::default();
        let mut script_roots = FxHashSet::default();
        // The crates of a package `--exclude` names are not checked.
        let mut excluded_roots = FxHashSet::default();
        let mut manifests = FxHashMap::default();
        for workspace in checkouts.loaded.workspaces() {
            let ProjectWorkspaceKind::Cargo { cargo, .. } = &workspace.kind else { continue };
            let root: &Path = cargo.workspace_root().as_ref();
            for file in ["Cargo.lock", ".cargo/config.toml", ".cargo/config"] {
                manifests.insert(root.join(file), None);
            }
            for package in cargo.packages().filter(|it| cargo[*it].is_local) {
                manifests.insert(cargo[package].manifest.to_path_buf().into(), None);
                let excluded = selection.excludes.contains(&cargo[package].name);
                for &target in &cargo[package].targets {
                    let target = &cargo[target];
                    if excluded {
                        excluded_roots.insert(PathBuf::from(target.root.clone()));
                    }
                    let runs = matches!(
                        target.kind,
                        TargetKind::BuildScript | TargetKind::Lib { is_proc_macro: true }
                    );
                    if runs {
                        ran_roots.insert(PathBuf::from(target.root.clone()));
                    }
                    if target.kind == TargetKind::BuildScript {
                        script_roots.insert(PathBuf::from(target.root.clone()));
                    }
                }
            }
        }
        for (path, when) in &mut manifests {
            *when = modified(path);
        }
        let path_of = |file: vfs::FileId| -> Option<PathBuf> {
            Some(vfs.file_path(file).as_path()?.to_path_buf().into())
        };
        let (mut checked, mut ran, mut dirs, mut crates) =
            (Vec::new(), FxHashSet::default(), Vec::new(), 0);
        let mut linted = Vec::new();
        hir::attach_db(db, || {
            for &member in members {
                let krate = hir::Crate::from(member);
                if !krate.origin(db).is_local() {
                    continue;
                }
                // Metadata includes dev targets even when the build loads none of their
                // dev-dependencies. A plain check leaves them alone, as cargo does. Use
                // the crate's kind: a test and a binary can share the same root file.
                if !selection.dev_deps
                    && matches!(
                        krate.target_kind(db),
                        TargetKind::Example | TargetKind::Test | TargetKind::Bench
                    )
                {
                    continue;
                }
                let root_file = krate.root_file(db);
                if path_of(root_file).is_some_and(|it| excluded_roots.contains(&it)) {
                    continue;
                }
                if !path_of(root_file).is_some_and(|it| script_roots.contains(&it)) {
                    linted.push(member);
                }
                let runs = path_of(root_file).is_some_and(|it| ran_roots.contains(&it));
                let mut of_it: Vec<vfs::FileId> = krate
                    .modules(db)
                    .into_iter()
                    .map(|it| it.definition_source_file_id(db).original_file(db).file_id(db))
                    .collect();
                of_it.sort_unstable();
                of_it.dedup();
                match runs {
                    true => ran.extend(of_it),
                    false => {
                        crates += 1;
                        if let Some(dir) = path_of(root_file).as_deref().and_then(Path::parent) {
                            dirs.push(dir.to_owned());
                        }
                        checked.extend(of_it);
                    }
                }
            }
        });
        checked.sort_unstable();
        checked.dedup();
        dirs.sort();
        dirs.dedup();
        // A directory below another is walked with it.
        let outer: Vec<PathBuf> = dirs
            .iter()
            .filter(|dir| !dirs.iter().any(|it| it != *dir && dir.starts_with(it)))
            .cloned()
            .collect();
        let loaded =
            vfs.iter().filter_map(|(_, path)| Some(path.as_path()?.to_path_buf().into())).collect();
        let located = vfs
            .iter()
            .filter_map(|(id, path)| Some((id, path.as_path()?.to_path_buf().into())))
            .collect();
        Checker {
            files,
            checked,
            crates,
            ran,
            dirs: outer,
            loaded,
            manifests,
            sources: Sources { paths },
            root,
            lints_capped,
            linted,
            located,
        }
    }

    /// Takes in the source as it is now, or says why only loading it again does.
    fn refresh(&mut self, db: &mut RootDatabase) -> Option<String> {
        for (path, when) in &self.manifests {
            if modified(path) != *when {
                return Some(format!("{} changed", path.display()));
            }
        }
        if let Some(new) = self.dirs.iter().find_map(|dir| new_source(dir, &self.loaded)) {
            return Some(format!("{} is new", new.display()));
        }
        let mut change = ChangeWithProcMacros::default();
        for watched in &mut self.files {
            let Watched::Source(id) = watched.file else { continue };
            let Some(now) = modified(&watched.path) else {
                return Some(format!("{} is gone", watched.path.display()));
            };
            if now == watched.mtime {
                continue;
            }
            watched.mtime = now;
            let Ok(text) = crate::source_on_disk(&watched.path) else {
                return Some(format!("{} can't be read", watched.path.display()));
            };
            if *text == **db.file_text(id).text(db) {
                continue;
            }
            if self.ran.contains(&id) {
                return Some(format!("{} runs as it was built", watched.path.display()));
            }
            change.change_file(id, Some(text));
        }
        db.apply_change(change);
        None
    }

    /// `ok`, or the errors in the source as rustc writes them.
    fn verdict(&self, db: &RootDatabase) -> String {
        match self.refused(db) {
            Some(refused) => refused.reply(),
            None => "ok".to_owned(),
        }
    }

    /// The errors in the source, `None` when it compiles.
    fn refused(&self, db: &RootDatabase) -> Option<crate::Refused> {
        let broken = crate::broken_in(
            db,
            &self.checked,
            &self.sources,
            &self.root,
            None,
            !self.lints_capped,
        );
        hir::attach_db(db, || {
            crate::refusal(db, &self.checked, &self.sources, &self.root, broken, None)
        })
    }

    /// The answer to the lint request `ask`: what blaze's clippy finds in the crates.
    fn lints(&self, db: &RootDatabase, ask: &str) -> String {
        let ask: blaze_lints::serve::Ask = match serde_json::from_str(ask) {
            Ok(ask) => ask,
            Err(error) => return format!("the lint request does not read: {error}"),
        };
        let path_of = |file: vfs::FileId| self.located.get(&file).cloned();
        let answer = blaze_lints::serve::answer(db, &self.linted, &self.root, &path_of, &ask);
        format!("{LINT}{}", serde_json::to_string(&answer).unwrap_or_default())
    }
}

fn modified(path: &Path) -> Option<SystemTime> {
    std::fs::metadata(path).and_then(|it| it.modified()).ok()
}

/// A Rust source file below `dir` that was not loaded. What a build made is not looked in.
fn new_source(dir: &Path, loaded: &FxHashSet<PathBuf>) -> Option<PathBuf> {
    let mut dirs = vec![dir.to_owned()];
    while let Some(dir) = dirs.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else { continue };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            let name = name.to_string_lossy();
            match entry.file_type() {
                Ok(kind) if kind.is_dir() => {
                    if !name.starts_with('.') && name != "target" {
                        dirs.push(path);
                    }
                }
                Ok(_) if name.ends_with(".rs") && !loaded.contains(&path) => return Some(path),
                _ => {}
            }
        }
    }
    None
}
