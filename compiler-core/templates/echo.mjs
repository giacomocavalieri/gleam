function echo(value) {
  const string = $inspect(value);
  if (typeof process === "object" && process.stderr?.write) {
    // If we're in Node.js, use `stderr`
    process.stderr.write(string + "\n");
  } else if (typeof Deno === "object") {
    // If we're in Deno, use `stderr`
    Deno.stderr.writeSync(new TextEncoder().encode(string + "\n"));
  } else {
    // Otherwise, use `console.log`
    console.log(string);
  }

  return value;
}

function $inspectString(str) {
  let new_str = '"';
  for (let i = 0; i < str.length; i++) {
    let char = str[i];
    if (char == "\n") new_str += "\\n";
    else if (char == "\r") new_str += "\\r";
    else if (char == "\t") new_str += "\\t";
    else if (char == "\f") new_str += "\\f";
    else if (char == "\\") new_str += "\\\\";
    else if (char == '"') new_str += '\\"';
    else if (char < " " || (char > "~" && char < "\u{00A0}")) {
      new_str += "\\u{" + char.charCodeAt(0).toString(16).toUpperCase().padStart(4, "0") + "}";
    } else {
      new_str += char;
    }
  }
  new_str += '"';
  return new_str;
}

function $inspectDict(map) {
  let body = "dict.from_list([";
  let first = true;
  map.forEach((value, key) => {
    if (!first) body = body + ", ";
    body = body + "#(" + $inspect(key) + ", " + $inspect(value) + ")";
    first = false;
  });
  return body + "])";
}

function $inspectCustomType(record) {
  const props = Object.keys(record)
    .map((label) => {
      const value = $inspect(record[label]);
      return isNaN(parseInt(label)) ? `${label}: ${value}` : value;
    })
    .join(", ");
  return props ? `${record.constructor.name}(${props})` : record.constructor.name;
}

function $inspectObject(v) {
  const name = Object.getPrototypeOf(v)?.constructor?.name || "Object";
  const props = [];
  for (const k of Object.keys(v)) {
    props.push(`${$inspect(k)}: ${$inspect(v[k])}`);
  }
  const body = props.length ? " " + props.join(", ") + " " : "";
  const head = name === "Object" ? "" : name + " ";
  return `//js(${head}{${body}})`;
}

function $inspect(v) {
  const t = typeof v;
  if (v === true) return "True";
  if (v === false) return "False";
  if (v === null) return "//js(null)";
  if (v === undefined) return "Nil";
  if (t === "string") return $inspectString(v);
  if (t === "bigint" || t === "number") return v.toString();
  if (Array.isArray(v)) return `#(${v.map($inspect).join(", ")})`;
  if (v instanceof List) return `[${v.toArray().map($inspect).join(", ")}]`;
  if (v instanceof UtfCodepoint) return `//utfcodepoint(${String.fromCodePoint(v.value)})`;
  if (v instanceof BitArray) return `<<${Array.from(v.buffer).join(", ")}>>`;
  if (v instanceof CustomType) return $inspectCustomType(v);
  if ($isDict(v)) return $inspectDict(v);
  if (v instanceof Set) return `//js(Set(${[...v].map($inspect).join(", ")}))`;
  if (v instanceof RegExp) return `//js(${v})`;
  if (v instanceof Date) return `//js(Date("${v.toISOString()}"))`;
  if (v instanceof Function) {
    const args = [];
    for (const i of Array(v.length).keys()) args.push(String.fromCharCode(i + 97));
    return `//fn(${args.join(", ")}) { ... }`;
  }
  return $inspectObject(v);
}

function $isDict(value) {
  try {
    // We can only check if an object is a stdlib Dict if it is one of the
    // project's dependencies.
    // The `Dict` class is the default export of `stdlib/dict.mjs`
    // that we import as `$stdlib$dict`.
    return value instanceof $stdlib$dict.default;
  } catch {
    // If stdlib is not one of the project's dependencies then `$stdlib$dict`
    // will not have been imported and the check will throw an exception meaning
    // we can't check if something is actually a `Dict`.
    return false;
  }
}