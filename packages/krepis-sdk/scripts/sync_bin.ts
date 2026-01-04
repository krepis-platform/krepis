const platform = `${Deno.build.os}-${Deno.build.arch}`;
const binDir = `./bin/${platform}`;
await Deno.mkdir(binDir, { recursive: true });

const src = `../../target/release/${Deno.build.os === "windows" ? "" : "lib"}krepis_kernel.${
  Deno.build.os === "windows" ? "dll" : Deno.build.os === "darwin" ? "dylib" : "so"
}`;

await Deno.copyFile(src, `${binDir}/${src.split('/').pop()}`);
console.log(`✅ Binary synced to ${binDir}`);