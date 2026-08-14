import { chooseComputerMove } from "./engine.mjs";

self.addEventListener("message", (event) => {
  const { id, state, options } = event.data ?? {};
  try {
    const result = chooseComputerMove(state, options);
    self.postMessage({ id, result });
  } catch (error) {
    self.postMessage({
      id,
      error: error instanceof Error ? error.message : String(error),
    });
  }
});
