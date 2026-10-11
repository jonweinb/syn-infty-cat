"""Include repo-root exercises/ in the MkDocs site.

docs_dir is lectures/, so these files are otherwise omitted.
"""

from pathlib import Path

from mkdocs.structure.files import File

REPO_ROOT = Path(__file__).resolve().parent
EXERCISES_DIR = REPO_ROOT / "exercises"


def on_files(files, config):
    dest_dir = config["site_dir"]
    use_directory_urls = config["use_directory_urls"]
    for path in sorted(EXERCISES_DIR.glob("*.rzk.md")):
        files.append(
            File(
                path=f"exercises/{path.name}",
                src_dir=str(REPO_ROOT),
                dest_dir=dest_dir,
                use_directory_urls=use_directory_urls,
            )
        )
    return files


def on_pre_page(page, config, files):
    src = page.file.src_uri
    if src.startswith("exercises/"):
        repo = (config.get("repo_url") or "").rstrip("/")
        if repo:
            page.edit_url = f"{repo}/edit/main/{src}"
    return page
