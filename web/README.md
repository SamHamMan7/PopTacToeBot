# Pop Tac Toe browser app

This directory is a no-build static website. It can be hosted directly on Cloudflare Pages, Neocities, GitHub Pages, or any ordinary static web host.

## Included

- Click or drag to place a checker
- Click or drag a checker during movement
- Undo and restart
- Checker count from 3 through 16
- Two-player mode with all rule selectors
- Browser-computer mode for the research ruleset
- Simultaneous popping, Torus/Klein wrapping, Reincarnation, Ringout, Blocked, post-pop win checks, repetition draws, and movement variants
- Background-worker AI so the page remains responsive
- A formal-verification status panel that does not overstate the current proof

## Important AI note

The current website uses a JavaScript alpha-beta preview. It is useful for the playable first release, but it is not yet the optimized C++ engine from the repository. The next engine step is to compile a small C++ binding layer plus the strong engine to WebAssembly and replace `ai-worker.mjs` with the WebAssembly worker.

## Test the rules engine

```text
node engine.test.mjs
```

The test file covers the most important C++ regression cases, including simultaneous pushes, edge behavior, post-pop wins, simultaneous-line draws, movement pops, and repetition identity.

## Deploy without a terminal

### Cloudflare Pages

1. In Cloudflare, open **Workers & Pages**.
2. Choose **Create application → Pages → Connect to Git**.
3. Select the GitHub repository.
4. Set the production branch to `main` after this change is merged.
5. Set the root directory to `web`.
6. Leave the build command blank.
7. Set the output directory to `.`.
8. Select **Save and Deploy**.

Cloudflare then redeploys automatically whenever `main` changes.

### Neocities

Upload the contents of this directory through the Neocities file dashboard. `index.html` must be at the site root, alongside `styles.css`, `app.mjs`, `engine.mjs`, and `ai-worker.mjs`.

## Files

- `index.html` — page structure, controls, rules, and proof-status explanation
- `styles.css` — responsive board and page styling
- `engine.mjs` — rule engine and browser alpha-beta preview
- `ai-worker.mjs` — background AI worker
- `app.mjs` — user interface, undo/history, repetition tracking, and mode handling
- `engine.test.mjs` — rules regression tests
