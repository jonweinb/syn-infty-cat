# syn-infty-cat

Lectures on synthetic ∞-category theory, written as literate [Rzk](https://rzk-lang.github.io/) Markdown.

The HTML notes are published at [jonweinb.github.io/syn-infty-cat](https://jonweinb.github.io/syn-infty-cat/).

## Lectures

- [Lecture 1: Introduction to homotopy type theory](lectures/01-rzk-hott.rzk.md)
- [Lecture 2: Simplicial homotopy type theory and Segal types](lectures/02-shott.rzk.md)
- [Lecture 3: Category theory with Segal types](lectures/03-more-segal.rzk.md)
- [Lecture 4: Discrete and Rezk types](lectures/04-disc-segal-rezk.rzk.md)

## Exercises

- [Associativity in Segal types](lectures/exercises/03a-associativity.rzk.md)

## Prerequisites

- [rzk](https://rzk-lang.github.io/rzk/en/latest/getting-started/install/) (the VS Code/Cursor rzk extension is enough)
- Python 3 with pip

## Typecheck

```sh
# if rzk is only via the editor extension:
export PATH="$HOME/Library/Application Support/Cursor/User/globalStorage/nikolaikudasovfizruk.rzk-1-experimental-highlighting/bin:$PATH"

rzk typecheck --allow-holes
```

Some constructions are left as `?` holes.

## Preview HTML

```sh
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
mkdocs serve
```

Then open the URL MkDocs prints (usually http://127.0.0.1:8000).

## GitHub Pages

Pushes to `main` build the MkDocs site and deploy it to the `gh-pages` branch. In the GitHub repo, set **Settings → Pages → Build and deployment → Source** to **Deploy from a branch**, branch `gh-pages` / `/ (root)`.
