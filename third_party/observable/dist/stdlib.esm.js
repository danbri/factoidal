var __defProp = Object.defineProperty;
var __export = (target, all) => {
  for (var name in all)
    __defProp(target, name, { get: all[name], enumerable: true });
};

// node_modules/d3-dsv/src/dsv.js
var EOL = {};
var EOF = {};
var QUOTE = 34;
var NEWLINE = 10;
var RETURN = 13;
function objectConverter(columns) {
  return new Function("d", "return {" + columns.map(function(name, i) {
    return JSON.stringify(name) + ": d[" + i + '] || ""';
  }).join(",") + "}");
}
function customConverter(columns, f) {
  var object = objectConverter(columns);
  return function(row, i) {
    return f(object(row), i, columns);
  };
}
function inferColumns(rows) {
  var columnSet = /* @__PURE__ */ Object.create(null), columns = [];
  rows.forEach(function(row) {
    for (var column in row) {
      if (!(column in columnSet)) {
        columns.push(columnSet[column] = column);
      }
    }
  });
  return columns;
}
function pad(value, width2) {
  var s = value + "", length = s.length;
  return length < width2 ? new Array(width2 - length + 1).join(0) + s : s;
}
function formatYear(year) {
  return year < 0 ? "-" + pad(-year, 6) : year > 9999 ? "+" + pad(year, 6) : pad(year, 4);
}
function formatDate(date) {
  var hours = date.getUTCHours(), minutes = date.getUTCMinutes(), seconds = date.getUTCSeconds(), milliseconds = date.getUTCMilliseconds();
  return isNaN(date) ? "Invalid Date" : formatYear(date.getUTCFullYear(), 4) + "-" + pad(date.getUTCMonth() + 1, 2) + "-" + pad(date.getUTCDate(), 2) + (milliseconds ? "T" + pad(hours, 2) + ":" + pad(minutes, 2) + ":" + pad(seconds, 2) + "." + pad(milliseconds, 3) + "Z" : seconds ? "T" + pad(hours, 2) + ":" + pad(minutes, 2) + ":" + pad(seconds, 2) + "Z" : minutes || hours ? "T" + pad(hours, 2) + ":" + pad(minutes, 2) + "Z" : "");
}
function dsv_default(delimiter) {
  var reFormat = new RegExp('["' + delimiter + "\n\r]"), DELIMITER = delimiter.charCodeAt(0);
  function parse(text4, f) {
    var convert, columns, rows = parseRows(text4, function(row, i) {
      if (convert) return convert(row, i - 1);
      columns = row, convert = f ? customConverter(row, f) : objectConverter(row);
    });
    rows.columns = columns || [];
    return rows;
  }
  function parseRows(text4, f) {
    var rows = [], N = text4.length, I = 0, n = 0, t, eof = N <= 0, eol = false;
    if (text4.charCodeAt(N - 1) === NEWLINE) --N;
    if (text4.charCodeAt(N - 1) === RETURN) --N;
    function token() {
      if (eof) return EOF;
      if (eol) return eol = false, EOL;
      var i, j = I, c;
      if (text4.charCodeAt(j) === QUOTE) {
        while (I++ < N && text4.charCodeAt(I) !== QUOTE || text4.charCodeAt(++I) === QUOTE) ;
        if ((i = I) >= N) eof = true;
        else if ((c = text4.charCodeAt(I++)) === NEWLINE) eol = true;
        else if (c === RETURN) {
          eol = true;
          if (text4.charCodeAt(I) === NEWLINE) ++I;
        }
        return text4.slice(j + 1, i - 1).replace(/""/g, '"');
      }
      while (I < N) {
        if ((c = text4.charCodeAt(i = I++)) === NEWLINE) eol = true;
        else if (c === RETURN) {
          eol = true;
          if (text4.charCodeAt(I) === NEWLINE) ++I;
        } else if (c !== DELIMITER) continue;
        return text4.slice(j, i);
      }
      return eof = true, text4.slice(j, N);
    }
    while ((t = token()) !== EOF) {
      var row = [];
      while (t !== EOL && t !== EOF) row.push(t), t = token();
      if (f && (row = f(row, n++)) == null) continue;
      rows.push(row);
    }
    return rows;
  }
  function preformatBody(rows, columns) {
    return rows.map(function(row) {
      return columns.map(function(column) {
        return formatValue(row[column]);
      }).join(delimiter);
    });
  }
  function format(rows, columns) {
    if (columns == null) columns = inferColumns(rows);
    return [columns.map(formatValue).join(delimiter)].concat(preformatBody(rows, columns)).join("\n");
  }
  function formatBody(rows, columns) {
    if (columns == null) columns = inferColumns(rows);
    return preformatBody(rows, columns).join("\n");
  }
  function formatRows(rows) {
    return rows.map(formatRow).join("\n");
  }
  function formatRow(row) {
    return row.map(formatValue).join(delimiter);
  }
  function formatValue(value) {
    return value == null ? "" : value instanceof Date ? formatDate(value) : reFormat.test(value += "") ? '"' + value.replace(/"/g, '""') + '"' : value;
  }
  return {
    parse,
    parseRows,
    format,
    formatBody,
    formatRows,
    formatRow,
    formatValue
  };
}

// node_modules/d3-dsv/src/csv.js
var csv = dsv_default(",");
var csvParse = csv.parse;
var csvParseRows = csv.parseRows;
var csvFormat = csv.format;
var csvFormatBody = csv.formatBody;
var csvFormatRows = csv.formatRows;
var csvFormatRow = csv.formatRow;
var csvFormatValue = csv.formatValue;

// node_modules/d3-dsv/src/tsv.js
var tsv = dsv_default("	");
var tsvParse = tsv.parse;
var tsvParseRows = tsv.parseRows;
var tsvFormat = tsv.format;
var tsvFormatBody = tsv.formatBody;
var tsvFormatRows = tsv.formatRows;
var tsvFormatRow = tsv.formatRow;
var tsvFormatValue = tsv.formatValue;

// node_modules/d3-dsv/src/autoType.js
function autoType(object) {
  for (var key in object) {
    var value = object[key].trim(), number, m;
    if (!value) value = null;
    else if (value === "true") value = true;
    else if (value === "false") value = false;
    else if (value === "NaN") value = NaN;
    else if (!isNaN(number = +value)) value = number;
    else if (m = value.match(/^([-+]\d{2})?\d{4}(-\d{2}(-\d{2})?)?(T\d{2}:\d{2}(:\d{2}(\.\d{3})?)?(Z|[-+]\d{2}:\d{2})?)?$/)) {
      if (fixtz && !!m[4] && !m[7]) value = value.replace(/-/g, "/").replace(/T/, " ");
      value = new Date(value);
    } else continue;
    object[key] = value;
  }
  return object;
}
var fixtz = (/* @__PURE__ */ new Date("2019-01-01T00:00")).getHours() || (/* @__PURE__ */ new Date("2019-07-01T00:00")).getHours();

// node_modules/@observablehq/stdlib/src/dependency.js
function dependency(name, version, main) {
  return {
    resolve(path = main) {
      return `${name}@${version}/${path}`;
    }
  };
}

// node_modules/@observablehq/stdlib/src/dependencies.js
var d3 = dependency("d3", "7.9.0", "dist/d3.min.js");
var inputs = dependency("@observablehq/inputs", "0.11.0", "dist/inputs.min.js");
var plot = dependency("@observablehq/plot", "0.6.16", "dist/plot.umd.min.js");
var graphviz = dependency("@observablehq/graphviz", "0.2.1", "dist/graphviz.min.js");
var highlight = dependency("@observablehq/highlight.js", "2.0.0", "highlight.min.js");
var katex = dependency("@observablehq/katex", "0.11.1", "dist/katex.min.js");
var lodash = dependency("lodash", "4.17.21", "lodash.min.js");
var htl = dependency("htl", "0.3.1", "dist/htl.min.js");
var jszip = dependency("jszip", "3.10.1", "dist/jszip.min.js");
var marked = dependency("marked", "0.3.12", "marked.min.js");
var sql = dependency("sql.js", "1.8.0", "dist/sql-wasm.js");
var vega = dependency("vega", "5.22.1", "build/vega.min.js");
var vegalite = dependency("vega-lite", "5.6.0", "build/vega-lite.min.js");
var vegaliteApi = dependency("vega-lite-api", "5.0.0", "build/vega-lite-api.min.js");
var arrow4 = dependency("apache-arrow", "4.0.1", "Arrow.es2015.min.js");
var arrow9 = dependency("apache-arrow", "9.0.0", "+esm");
var arrow11 = dependency("apache-arrow", "11.0.0", "+esm");
var arquero = dependency("arquero", "4.8.8", "dist/arquero.min.js");
var topojson = dependency("topojson-client", "3.1.0", "dist/topojson-client.min.js");
var exceljs = dependency("exceljs", "4.3.0", "dist/exceljs.min.js");
var mermaid = dependency("mermaid", "9.2.2", "dist/mermaid.min.js");
var leaflet = dependency("leaflet", "1.9.3", "dist/leaflet.js");
var duckdb = dependency("@duckdb/duckdb-wasm", "1.24.0", "+esm");

// node_modules/d3-require/src/index.mjs
var metas = /* @__PURE__ */ new Map();
var queue = [];
var map = queue.map;
var some = queue.some;
var hasOwnProperty = queue.hasOwnProperty;
var identifierRe = /^((?:@[^/@]+\/)?[^/@]+)(?:@([^/]+))?(?:\/(.*))?$/;
var versionRe = /^\d+\.\d+\.\d+(-[\w-.+]+)?$/;
var extensionRe = /(?:\.[^/]*|\/)$/;
var RequireError = class extends Error {
  constructor(message) {
    super(message);
  }
};
RequireError.prototype.name = RequireError.name;
function parseIdentifier(identifier) {
  const match = identifierRe.exec(identifier);
  return match && {
    name: match[1],
    version: match[2],
    path: match[3]
  };
}
function resolveFrom(origin = "https://cdn.jsdelivr.net/npm/", mains = ["unpkg", "jsdelivr", "browser", "main"]) {
  if (!/\/$/.test(origin)) throw new Error("origin lacks trailing slash");
  function main(meta) {
    for (const key of mains) {
      let value = meta[key];
      if (typeof value === "string") {
        if (value.startsWith("./")) value = value.slice(2);
        return extensionRe.test(value) ? value : `${value}.js`;
      }
    }
  }
  function resolveMeta(target) {
    const url2 = `${origin}${target.name}${target.version ? `@${target.version}` : ""}/package.json`;
    let meta = metas.get(url2);
    if (!meta) metas.set(url2, meta = fetch(url2).then((response) => {
      if (!response.ok) throw new RequireError("unable to load package.json");
      if (response.redirected && !metas.has(response.url)) metas.set(response.url, meta);
      return response.json();
    }));
    return meta;
  }
  return async function resolve2(name, base) {
    if (name.startsWith(origin)) name = name.substring(origin.length);
    if (/^(\w+:)|\/\//i.test(name)) return name;
    if (/^[.]{0,2}\//i.test(name)) return new URL(name, base == null ? location : base).href;
    if (!name.length || /^[\s._]/.test(name) || /\s$/.test(name)) throw new RequireError("illegal name");
    const target = parseIdentifier(name);
    if (!target) return `${origin}${name}`;
    if (!target.version && base != null && base.startsWith(origin)) {
      const meta2 = await resolveMeta(parseIdentifier(base.substring(origin.length)));
      target.version = meta2.dependencies && meta2.dependencies[target.name] || meta2.peerDependencies && meta2.peerDependencies[target.name];
    }
    if (target.path && !extensionRe.test(target.path)) target.path += ".js";
    if (target.path && target.version && versionRe.test(target.version)) return `${origin}${target.name}@${target.version}/${target.path}`;
    const meta = await resolveMeta(target);
    return `${origin}${meta.name}@${meta.version}/${target.path || main(meta) || "index.js"}`;
  };
}
var require2 = requireFrom(resolveFrom());
function requireFrom(resolver) {
  const cache = /* @__PURE__ */ new Map();
  const requireBase = requireRelative(null);
  function requireAbsolute(url2) {
    if (typeof url2 !== "string") return url2;
    let module = cache.get(url2);
    if (!module) cache.set(url2, module = new Promise((resolve2, reject) => {
      const script = document.createElement("script");
      script.onload = () => {
        try {
          resolve2(queue.pop()(requireRelative(url2)));
        } catch (error) {
          reject(new RequireError("invalid module"));
        }
        script.remove();
      };
      script.onerror = () => {
        reject(new RequireError("unable to load module"));
        script.remove();
      };
      script.async = true;
      script.src = url2;
      window.define = define;
      document.head.appendChild(script);
    }));
    return module;
  }
  function requireRelative(base) {
    return (name) => Promise.resolve(resolver(name, base)).then(requireAbsolute);
  }
  function requireAlias(aliases) {
    return requireFrom((name, base) => {
      if (name in aliases) {
        name = aliases[name], base = null;
        if (typeof name !== "string") return name;
      }
      return resolver(name, base);
    });
  }
  function require3(name) {
    return arguments.length > 1 ? Promise.all(map.call(arguments, requireBase)).then(merge) : requireBase(name);
  }
  require3.alias = requireAlias;
  require3.resolve = resolver;
  return require3;
}
function merge(modules) {
  const o = {};
  for (const m of modules) {
    for (const k in m) {
      if (hasOwnProperty.call(m, k)) {
        if (m[k] == null) Object.defineProperty(o, k, { get: getter(m, k) });
        else o[k] = m[k];
      }
    }
  }
  return o;
}
function getter(object, name) {
  return () => object[name];
}
function isbuiltin(name) {
  name = name + "";
  return name === "exports" || name === "module";
}
function define(name, dependencies, factory) {
  const n = arguments.length;
  if (n < 2) factory = name, dependencies = [];
  else if (n < 3) factory = dependencies, dependencies = typeof name === "string" ? [] : name;
  queue.push(some.call(dependencies, isbuiltin) ? (require3) => {
    const exports = {};
    const module = { exports };
    return Promise.all(map.call(dependencies, (name2) => {
      name2 = name2 + "";
      return name2 === "exports" ? exports : name2 === "module" ? module : require3(name2);
    })).then((dependencies2) => {
      factory.apply(null, dependencies2);
      return module.exports;
    });
  } : (require3) => {
    return Promise.all(map.call(dependencies, require3)).then((dependencies2) => {
      return typeof factory === "function" ? factory.apply(null, dependencies2) : factory;
    });
  });
}
define.amd = {};

// node_modules/@observablehq/stdlib/src/require.js
var cdn = "https://cdn.observableusercontent.com/npm/";
var requireDefault = require2;
function setDefaultRequire(require3) {
  requireDefault = require3;
}
function requirer(resolver) {
  return resolver == null ? requireDefault : requireFrom(resolver);
}

// node_modules/@observablehq/stdlib/src/sqlite.js
async function SQLite(require3) {
  const [init, dist] = await Promise.all([require3(sql.resolve()), require3.resolve(sql.resolve("dist/"))]);
  return init({ locateFile: (file) => `${dist}${file}` });
}
var SQLiteDatabaseClient = class _SQLiteDatabaseClient {
  constructor(db) {
    Object.defineProperties(this, {
      _db: { value: db }
    });
  }
  static async open(source) {
    const [SQL, buffer2] = await Promise.all([SQLite(requireDefault), Promise.resolve(source).then(load)]);
    return new _SQLiteDatabaseClient(new SQL.Database(buffer2));
  }
  async query(query, params) {
    return await exec(this._db, query, params);
  }
  async queryRow(query, params) {
    return (await this.query(query, params))[0] || null;
  }
  async explain(query, params) {
    const rows = await this.query(`EXPLAIN QUERY PLAN ${query}`, params);
    return element("pre", { className: "observablehq--inspect" }, [
      text(rows.map((row) => row.detail).join("\n"))
    ]);
  }
  async describeTables({ schema } = {}) {
    return this.query(`SELECT NULLIF(schema, 'main') AS schema, name FROM pragma_table_list() WHERE type = 'table'${schema == null ? "" : ` AND schema = ?`} AND name NOT LIKE 'sqlite_%' ORDER BY schema, name`, schema == null ? [] : [schema]);
  }
  async describeColumns({ schema, table } = {}) {
    if (table == null) throw new Error(`missing table`);
    const rows = await this.query(`SELECT name, type, "notnull" FROM pragma_table_info(?${schema == null ? "" : `, ?`}) ORDER BY cid`, schema == null ? [table] : [table, schema]);
    if (!rows.length) throw new Error(`table not found: ${table}`);
    return rows.map(({ name, type, notnull }) => ({ name, type: sqliteType(type), databaseType: type, nullable: !notnull }));
  }
  async describe(object) {
    const rows = await (object === void 0 ? this.query(`SELECT name FROM sqlite_master WHERE type = 'table'`) : this.query(`SELECT * FROM pragma_table_info(?)`, [object]));
    if (!rows.length) throw new Error("Not found");
    const { columns } = rows;
    return element("table", { value: rows }, [
      element("thead", [element("tr", columns.map((c) => element("th", [text(c)])))]),
      element("tbody", rows.map((r) => element("tr", columns.map((c) => element("td", [text(r[c])])))))
    ]);
  }
  async sql() {
    return this.query(...this.queryTag.apply(this, arguments));
  }
  queryTag(strings, ...params) {
    return [strings.join("?"), params];
  }
};
Object.defineProperty(SQLiteDatabaseClient.prototype, "dialect", {
  value: "sqlite"
});
function sqliteType(type) {
  switch (type) {
    case "NULL":
      return "null";
    case "INT":
    case "INTEGER":
    case "TINYINT":
    case "SMALLINT":
    case "MEDIUMINT":
    case "BIGINT":
    case "UNSIGNED BIG INT":
    case "INT2":
    case "INT8":
      return "integer";
    case "TEXT":
    case "CLOB":
      return "string";
    case "REAL":
    case "DOUBLE":
    case "DOUBLE PRECISION":
    case "FLOAT":
    case "NUMERIC":
      return "number";
    case "BLOB":
      return "buffer";
    case "DATE":
    case "DATETIME":
      return "string";
    // TODO convert strings to Date instances in sql.js
    default:
      return /^(?:(?:(?:VARYING|NATIVE) )?CHARACTER|(?:N|VAR|NVAR)CHAR)\(/.test(type) ? "string" : /^(?:DECIMAL|NUMERIC)\(/.test(type) ? "number" : "other";
  }
}
function load(source) {
  return typeof source === "string" ? fetch(source).then(load) : source instanceof Response || source instanceof Blob ? source.arrayBuffer().then(load) : source instanceof ArrayBuffer ? new Uint8Array(source) : source;
}
async function exec(db, query, params) {
  const [result] = await db.exec(query, params);
  if (!result) return [];
  const { columns, values } = result;
  const rows = values.map((row) => Object.fromEntries(row.map((value, i) => [columns[i], value])));
  rows.columns = columns;
  return rows;
}
function element(name, props, children) {
  if (arguments.length === 2) children = props, props = void 0;
  const element3 = document.createElement(name);
  if (props !== void 0) for (const p in props) element3[p] = props[p];
  if (children !== void 0) for (const c of children) element3.appendChild(c);
  return element3;
}
function text(value) {
  return document.createTextNode(value);
}

// node_modules/d3-array/src/ascending.js
function ascending(a, b) {
  return a == null || b == null ? NaN : a < b ? -1 : a > b ? 1 : a >= b ? 0 : NaN;
}

// node_modules/d3-array/src/greatest.js
function greatest(values, compare = ascending) {
  let max;
  let defined2 = false;
  if (compare.length === 1) {
    let maxValue;
    for (const element3 of values) {
      const value = compare(element3);
      if (defined2 ? ascending(value, maxValue) > 0 : ascending(value, value) === 0) {
        max = element3;
        maxValue = value;
        defined2 = true;
      }
    }
  } else {
    for (const value of values) {
      if (defined2 ? compare(value, max) > 0 : compare(value, value) === 0) {
        max = value;
        defined2 = true;
      }
    }
  }
  return max;
}

// node_modules/d3-array/src/reverse.js
function reverse(values) {
  if (typeof values[Symbol.iterator] !== "function") throw new TypeError("values is not iterable");
  return Array.from(values).reverse();
}

// node_modules/@observablehq/stdlib/src/arquero.js
function isArqueroTable(value) {
  return value && typeof value.toArrowBuffer === "function";
}

// node_modules/@observablehq/stdlib/src/arrow.js
function isArrowTable(value) {
  return value && typeof value.getChild === "function" && typeof value.toArray === "function" && value.schema && Array.isArray(value.schema.fields);
}
function getArrowTableSchema(table) {
  return table.schema.fields.map(getArrowFieldSchema);
}
function getArrowFieldSchema(field) {
  return {
    name: field.name,
    type: getArrowType(field.type),
    nullable: field.nullable,
    databaseType: String(field.type)
  };
}
function getArrowType(type) {
  switch (type.typeId) {
    case 2:
      return "integer";
    case 3:
    // Float
    case 7:
      return "number";
    case 4:
    // Binary
    case 15:
      return "buffer";
    case 5:
      return "string";
    case 6:
      return "boolean";
    case 8:
    // Date
    case 9:
    // Time
    case 10:
      return "date";
    case 12:
    // List
    case 16:
      return "array";
    case 13:
    // Struct
    case 14:
      return "object";
    case 11:
    // Interval
    case 17:
    // Map
    default:
      return "other";
  }
}
async function loadArrow() {
  return await import(`${cdn}${arrow11.resolve()}`);
}

// node_modules/@observablehq/stdlib/src/duckdb.js
var promise;
var DuckDBClient = class _DuckDBClient {
  constructor(db) {
    Object.defineProperties(this, {
      _db: { value: db }
    });
  }
  async queryStream(query, params) {
    const connection = await this._db.connect();
    let reader, batch;
    try {
      if (params?.length > 0) {
        const statement = await connection.prepare(query);
        reader = await statement.send(...params);
      } else {
        reader = await connection.send(query);
      }
      batch = await reader.next();
      if (batch.done) throw new Error("missing first batch");
    } catch (error) {
      await connection.close();
      throw error;
    }
    return {
      schema: getArrowTableSchema(batch.value),
      async *readRows() {
        try {
          while (!batch.done) {
            yield batch.value.toArray();
            batch = await reader.next();
          }
        } finally {
          await connection.close();
        }
      }
    };
  }
  async query(query, params) {
    const result = await this.queryStream(query, params);
    const results = [];
    for await (const rows of result.readRows()) {
      for (const row of rows) {
        results.push(row);
      }
    }
    results.schema = result.schema;
    return results;
  }
  async queryRow(query, params) {
    const result = await this.queryStream(query, params);
    const reader = result.readRows();
    try {
      const { done, value } = await reader.next();
      return done || !value.length ? null : value[0];
    } finally {
      await reader.return();
    }
  }
  async sql(strings, ...args) {
    return await this.query(strings.join("?"), args);
  }
  queryTag(strings, ...params) {
    return [strings.join("?"), params];
  }
  escape(name) {
    return `"${name}"`;
  }
  async describeTables() {
    const tables = await this.query(`SHOW TABLES`);
    return tables.map(({ name }) => ({ name }));
  }
  async describeColumns({ table } = {}) {
    const columns = await this.query(`DESCRIBE ${this.escape(table)}`);
    return columns.map(({ column_name, column_type, null: nullable }) => ({
      name: column_name,
      type: getDuckDBType(column_type),
      nullable: nullable !== "NO",
      databaseType: column_type
    }));
  }
  static async of(sources = {}, config = {}) {
    const db = await createDuckDB();
    if (config.query?.castTimestampToDate === void 0) {
      config = { ...config, query: { ...config.query, castTimestampToDate: true } };
    }
    if (config.query?.castBigIntToDouble === void 0) {
      config = { ...config, query: { ...config.query, castBigIntToDouble: true } };
    }
    await db.open(config);
    await Promise.all(
      Object.entries(sources).map(async ([name, source]) => {
        if (source instanceof FileAttachment) {
          await insertFile(db, name, source);
        } else if (isArrowTable(source)) {
          await insertArrowTable(db, name, source);
        } else if (Array.isArray(source)) {
          await insertArray(db, name, source);
        } else if (isArqueroTable(source)) {
          await insertArqueroTable(db, name, source);
        } else if ("data" in source) {
          const { data, ...options } = source;
          if (isArrowTable(data)) {
            await insertArrowTable(db, name, data, options);
          } else {
            await insertArray(db, name, data, options);
          }
        } else if ("file" in source) {
          const { file, ...options } = source;
          await insertFile(db, name, file, options);
        } else {
          throw new Error(`invalid source: ${source}`);
        }
      })
    );
    return new _DuckDBClient(db);
  }
};
Object.defineProperty(DuckDBClient.prototype, "dialect", {
  value: "duckdb"
});
async function insertFile(database, name, file, options) {
  const url2 = await file.url();
  if (url2.startsWith("blob:")) {
    const buffer2 = await file.arrayBuffer();
    await database.registerFileBuffer(file.name, new Uint8Array(buffer2));
  } else {
    await database.registerFileURL(file.name, new URL(url2, location).href, 4);
  }
  const connection = await database.connect();
  try {
    switch (file.mimeType) {
      case "text/csv":
      case "text/tab-separated-values": {
        return await connection.insertCSVFromPath(file.name, {
          name,
          schema: "main",
          ...options
        }).catch(async (error) => {
          if (error.toString().includes("Could not convert")) {
            return await insertUntypedCSV(connection, file, name);
          }
          throw error;
        });
      }
      case "application/json":
        return await connection.insertJSONFromPath(file.name, {
          name,
          schema: "main",
          ...options
        });
      default:
        if (/\.arrow$/i.test(file.name)) {
          const buffer2 = new Uint8Array(await file.arrayBuffer());
          return await connection.insertArrowFromIPCStream(buffer2, {
            name,
            schema: "main",
            ...options
          });
        }
        if (/\.parquet$/i.test(file.name)) {
          return await connection.query(
            `CREATE VIEW '${name}' AS SELECT * FROM parquet_scan('${file.name}')`
          );
        }
        throw new Error(`unknown file type: ${file.mimeType}`);
    }
  } finally {
    await connection.close();
  }
}
async function insertUntypedCSV(connection, file, name) {
  const statement = await connection.prepare(
    `CREATE TABLE '${name}' AS SELECT * FROM read_csv_auto(?, ALL_VARCHAR=TRUE)`
  );
  return await statement.send(file.name);
}
async function insertArrowTable(database, name, table, options) {
  const connection = await database.connect();
  try {
    await connection.insertArrowTable(table, {
      name,
      schema: "main",
      ...options
    });
  } finally {
    await connection.close();
  }
}
async function insertArqueroTable(database, name, source) {
  const arrow = await loadArrow();
  const table = arrow.tableFromIPC(source.toArrowBuffer());
  return await insertArrowTable(database, name, table);
}
async function insertArray(database, name, array, options) {
  const arrow = await loadArrow();
  const table = arrow.tableFromJSON(array);
  return await insertArrowTable(database, name, table, options);
}
async function loadDuckDB() {
  const module = await import(`${cdn}${duckdb.resolve()}`);
  const bundle = await module.selectBundle({
    mvp: {
      mainModule: `${cdn}${duckdb.resolve("dist/duckdb-mvp.wasm")}`,
      mainWorker: `${cdn}${duckdb.resolve("dist/duckdb-browser-mvp.worker.js")}`
    },
    eh: {
      mainModule: `${cdn}${duckdb.resolve("dist/duckdb-eh.wasm")}`,
      mainWorker: `${cdn}${duckdb.resolve("dist/duckdb-browser-eh.worker.js")}`
    }
  });
  const logger = new module.ConsoleLogger();
  return { module, bundle, logger };
}
async function createDuckDB() {
  if (promise === void 0) promise = loadDuckDB();
  const { module, bundle, logger } = await promise;
  const worker2 = await module.createWorker(bundle.mainWorker);
  const db = new module.AsyncDuckDB(logger, worker2);
  await db.instantiate(bundle.mainModule);
  return db;
}
function getDuckDBType(type) {
  switch (type) {
    case "BIGINT":
    case "HUGEINT":
    case "UBIGINT":
      return "bigint";
    case "DOUBLE":
    case "REAL":
    case "FLOAT":
      return "number";
    case "INTEGER":
    case "SMALLINT":
    case "TINYINT":
    case "USMALLINT":
    case "UINTEGER":
    case "UTINYINT":
      return "integer";
    case "BOOLEAN":
      return "boolean";
    case "DATE":
    case "TIMESTAMP":
    case "TIMESTAMP WITH TIME ZONE":
      return "date";
    case "VARCHAR":
    case "UUID":
      return "string";
    // case "BLOB":
    // case "INTERVAL":
    // case "TIME":
    default:
      if (/^DECIMAL\(/.test(type)) return "integer";
      return "other";
  }
}

// node_modules/@observablehq/stdlib/src/table.js
var nChecks = 20;
function isDatabaseClient(value, mode) {
  return value && (typeof value.sql === "function" || typeof value.queryTag === "function" && (typeof value.query === "function" || typeof value.queryStream === "function")) && (mode !== "table" || typeof value.describeColumns === "function") && value !== __query;
}
function isDataArray(value) {
  return Array.isArray(value) && (isQueryResultSetSchema(value.schema) || isQueryResultSetColumns(value.columns) || arrayContainsObjects(value) || arrayContainsPrimitives(value) || arrayContainsDates(value)) || isTypedArray(value);
}
function arrayContainsObjects(value) {
  const n = Math.min(nChecks, value.length);
  for (let i = 0; i < n; ++i) {
    const v = value[i];
    if (v === null || typeof v !== "object") return false;
  }
  return n > 0 && objectHasEnumerableKeys(value[0]);
}
function objectHasEnumerableKeys(value) {
  for (const _ in value) return true;
  return false;
}
function isQueryResultSetSchema(schemas) {
  return Array.isArray(schemas) && schemas.every(isColumnSchema);
}
function isQueryResultSetColumns(columns) {
  return Array.isArray(columns) && columns.every((name) => typeof name === "string");
}
function isColumnSchema(schema) {
  return schema && typeof schema.name === "string" && typeof schema.type === "string";
}
function arrayIsPrimitive(value) {
  return isTypedArray(value) || arrayContainsPrimitives(value) || arrayContainsDates(value);
}
function arrayContainsPrimitives(value) {
  const n = Math.min(nChecks, value.length);
  if (!(n > 0)) return false;
  let type;
  let hasPrimitive = false;
  for (let i = 0; i < n; ++i) {
    const v = value[i];
    if (v == null) continue;
    const t = typeof v;
    if (type === void 0) {
      switch (t) {
        case "number":
        case "boolean":
        case "string":
        case "bigint":
          type = t;
          break;
        default:
          return false;
      }
    } else if (t !== type) {
      return false;
    }
    hasPrimitive = true;
  }
  return hasPrimitive;
}
function arrayContainsDates(value) {
  const n = Math.min(nChecks, value.length);
  if (!(n > 0)) return false;
  let hasDate = false;
  for (let i = 0; i < n; ++i) {
    const v = value[i];
    if (v == null) continue;
    if (!(v instanceof Date)) return false;
    hasDate = true;
  }
  return hasDate;
}
function isTypedArray(value) {
  return value instanceof Int8Array || value instanceof Int16Array || value instanceof Int32Array || value instanceof Uint8Array || value instanceof Uint8ClampedArray || value instanceof Uint16Array || value instanceof Uint32Array || value instanceof Float32Array || value instanceof Float64Array;
}
var __query = Object.assign(
  async (source, operations, invalidation, name) => {
    source = await loadTableDataSource(await source, name);
    if (isDatabaseClient(source)) return evaluateQuery(source, makeQueryTemplate(operations, source), invalidation);
    if (isDataArray(source)) return __table(source, operations);
    if (!source) throw new Error("missing data source");
    throw new Error("invalid data source");
  },
  {
    sql(source, invalidation, name) {
      return async function() {
        return evaluateQuery(await loadSqlDataSource(await source, name), arguments, invalidation);
      };
    }
  }
);
async function loadDataSource(source, mode, name) {
  switch (mode) {
    case "chart":
      return loadChartDataSource(source);
    case "table":
      return loadTableDataSource(source, name);
    case "sql":
      return loadSqlDataSource(source, name);
  }
  return source;
}
function sourceCache(loadSource) {
  const cache = /* @__PURE__ */ new WeakMap();
  return (source, name) => {
    if (!source || typeof source !== "object") throw new Error("invalid data source");
    let promise2 = cache.get(source);
    if (!promise2 || isDataArray(source) && source.length !== promise2._numRows) {
      promise2 = loadSource(source, name);
      promise2._numRows = source.length;
      cache.set(source, promise2);
    }
    return promise2;
  };
}
var loadChartDataSource = sourceCache(async (source) => {
  if (source instanceof FileAttachment) {
    switch (source.mimeType) {
      case "text/csv":
        return source.csv({ typed: "auto" });
      case "text/tab-separated-values":
        return source.tsv({ typed: "auto" });
      case "application/json":
        return source.json();
    }
    throw new Error(`unsupported file type: ${source.mimeType}`);
  }
  return source;
});
var loadTableDataSource = sourceCache(async (source, name) => {
  if (source instanceof FileAttachment) {
    switch (source.mimeType) {
      case "text/csv":
        return source.csv();
      case "text/tab-separated-values":
        return source.tsv();
      case "application/json":
        return source.json();
      case "application/x-sqlite3":
        return source.sqlite();
    }
    if (/\.(arrow|parquet)$/i.test(source.name)) return loadDuckDBClient(source, name);
    throw new Error(`unsupported file type: ${source.mimeType}`);
  }
  if (isArrowTable(source) || isArqueroTable(source)) return loadDuckDBClient(source, name);
  if (isDataArray(source) && arrayIsPrimitive(source))
    return Array.from(source, (value) => ({ value }));
  return source;
});
var loadSqlDataSource = sourceCache(async (source, name) => {
  if (source instanceof FileAttachment) {
    switch (source.mimeType) {
      case "text/csv":
      case "text/tab-separated-values":
      case "application/json":
        return loadDuckDBClient(source, name);
      case "application/x-sqlite3":
        return source.sqlite();
    }
    if (/\.(arrow|parquet)$/i.test(source.name)) return loadDuckDBClient(source, name);
    throw new Error(`unsupported file type: ${source.mimeType}`);
  }
  if (isDataArray(source)) return loadDuckDBClient(await asArrowTable(source, name), name);
  if (isArrowTable(source) || isArqueroTable(source)) return loadDuckDBClient(source, name);
  return source;
});
async function asArrowTable(array, name) {
  const arrow = await loadArrow();
  return arrayIsPrimitive(array) ? arrow.tableFromArrays({ [name]: array }) : arrow.tableFromJSON(array);
}
function loadDuckDBClient(source, name = source instanceof FileAttachment ? getFileSourceName(source) : "__table") {
  return DuckDBClient.of({ [name]: source });
}
function getFileSourceName(file) {
  return file.name.replace(/@\d+(?=\.|$)/, "").replace(/\.\w+$/, "");
}
async function evaluateQuery(source, args, invalidation) {
  if (!source) throw new Error("missing data source");
  if (typeof source.queryTag === "function") {
    const abortController = new AbortController();
    const options = { signal: abortController.signal };
    invalidation.then(() => abortController.abort("invalidated"));
    if (typeof source.queryStream === "function") {
      return accumulateQuery(
        source.queryStream(...source.queryTag.apply(source, args), options)
      );
    }
    if (typeof source.query === "function") {
      return source.query(...source.queryTag.apply(source, args), options);
    }
  }
  if (typeof source.sql === "function") {
    return source.sql.apply(source, args);
  }
  throw new Error("source does not implement query, queryStream, or sql");
}
async function* accumulateQuery(queryRequest) {
  let then = performance.now();
  const queryResponse = await queryRequest;
  const values = [];
  values.done = false;
  values.error = null;
  values.schema = queryResponse.schema;
  try {
    for await (const rows of queryResponse.readRows()) {
      if (performance.now() - then > 150 && values.length > 0) {
        yield values;
        then = performance.now();
      }
      for (const value of rows) {
        values.push(value);
      }
    }
    values.done = true;
    yield values;
  } catch (error) {
    values.error = error;
    yield values;
  }
}
function makeQueryTemplate(operations, source) {
  const escaper = typeof source.escape === "function" ? source.escape : (i) => i;
  const { select: select2, from, filter: filter2, sort, slice } = operations;
  if (!from.table)
    throw new Error("missing from table");
  if (select2.columns && select2.columns.length === 0)
    throw new Error("at least one column must be selected");
  const names = new Map(operations.names?.map(({ column, name }) => [column, name]));
  const columns = select2.columns ? select2.columns.map((column) => {
    const override = names.get(column);
    return override ? `${escaper(column)} AS ${escaper(override)}` : escaper(column);
  }).join(", ") : "*";
  const args = [
    [`SELECT ${columns} FROM ${formatTable(from.table, escaper)}`]
  ];
  for (let i = 0; i < filter2.length; ++i) {
    appendSql(i ? `
AND ` : `
WHERE `, args);
    appendWhereEntry(filter2[i], args, escaper);
  }
  for (let i = 0; i < sort.length; ++i) {
    appendSql(i ? `, ` : `
ORDER BY `, args);
    appendOrderBy(sort[i], args, escaper);
  }
  if (source.dialect === "mssql" || source.dialect === "oracle") {
    if (slice.to !== null || slice.from !== null) {
      if (!sort.length) {
        if (!select2.columns)
          throw new Error(
            "at least one column must be explicitly specified. Received '*'."
          );
        appendSql(`
ORDER BY `, args);
        appendOrderBy(
          { column: select2.columns[0], direction: "ASC" },
          args,
          escaper
        );
      }
      appendSql(`
OFFSET ${slice.from || 0} ROWS`, args);
      appendSql(
        `
FETCH NEXT ${slice.to !== null ? slice.to - (slice.from || 0) : 1e9} ROWS ONLY`,
        args
      );
    }
  } else {
    if (slice.to !== null || slice.from !== null) {
      appendSql(
        `
LIMIT ${slice.to !== null ? slice.to - (slice.from || 0) : 1e9}`,
        args
      );
    }
    if (slice.from !== null) {
      appendSql(` OFFSET ${slice.from}`, args);
    }
  }
  return args;
}
function formatTable(table, escaper) {
  if (typeof table === "object") {
    let from = "";
    if (table.database != null) from += escaper(table.database) + ".";
    if (table.schema != null) from += escaper(table.schema) + ".";
    from += escaper(table.table);
    return from;
  } else {
    return escaper(table);
  }
}
function appendSql(sql2, args) {
  const strings = args[0];
  strings[strings.length - 1] += sql2;
}
function appendOrderBy({ column, direction }, args, escaper) {
  appendSql(`${escaper(column)} ${direction.toUpperCase()}`, args);
}
function appendWhereEntry({ type, operands }, args, escaper) {
  if (operands.length < 1) throw new Error("Invalid operand length");
  if (operands.length === 1 || type === "v" || type === "nv") {
    appendOperand(operands[0], args, escaper);
    switch (type) {
      case "n":
      case "nv":
        appendSql(` IS NULL`, args);
        return;
      case "nn":
      case "v":
        appendSql(` IS NOT NULL`, args);
        return;
      default:
        throw new Error("Invalid filter operation");
    }
  }
  if (operands.length === 2) {
    if (["in", "nin"].includes(type)) {
    } else if (["c", "nc"].includes(type)) {
      appendOperand(operands[0], args, escaper);
      switch (type) {
        case "c":
          appendSql(` LIKE `, args);
          break;
        case "nc":
          appendSql(` NOT LIKE `, args);
          break;
      }
      appendOperand(likeOperand(operands[1]), args, escaper);
      return;
    } else {
      appendOperand(operands[0], args, escaper);
      switch (type) {
        case "eq":
          appendSql(` = `, args);
          break;
        case "ne":
          appendSql(` <> `, args);
          break;
        case "gt":
          appendSql(` > `, args);
          break;
        case "lt":
          appendSql(` < `, args);
          break;
        case "gte":
          appendSql(` >= `, args);
          break;
        case "lte":
          appendSql(` <= `, args);
          break;
        default:
          throw new Error("Invalid filter operation");
      }
      appendOperand(operands[1], args, escaper);
      return;
    }
  }
  appendOperand(operands[0], args, escaper);
  switch (type) {
    case "in":
      appendSql(` IN (`, args);
      break;
    case "nin":
      appendSql(` NOT IN (`, args);
      break;
    default:
      throw new Error("Invalid filter operation");
  }
  appendListOperands(operands.slice(1), args);
  appendSql(")", args);
}
function appendOperand(o, args, escaper) {
  if (o.type === "column") {
    appendSql(escaper(o.value), args);
  } else {
    args.push(o.value);
    args[0].push("");
  }
}
function appendListOperands(ops, args) {
  let first = true;
  for (const op of ops) {
    if (first) first = false;
    else appendSql(",", args);
    args.push(op.value);
    args[0].push("");
  }
}
function likeOperand(operand) {
  return { ...operand, value: `%${operand.value}%` };
}
function defined(a, b) {
  return (a == null || !(a >= a)) - (b == null || !(b >= b));
}
function ascendingDefined(a, b) {
  return defined(a, b) || (a < b ? -1 : a > b ? 1 : 0);
}
function descendingDefined(a, b) {
  return defined(a, b) || (a > b ? -1 : a < b ? 1 : 0);
}
var isValidNumber = (value) => typeof value === "number" && !Number.isNaN(value);
var isValidInteger = (value) => Number.isInteger(value) && !Number.isNaN(value);
var isValidString = (value) => typeof value === "string";
var isValidBoolean = (value) => typeof value === "boolean";
var isValidBigint = (value) => typeof value === "bigint";
var isValidDate = (value) => value instanceof Date && !isNaN(value);
var isValidBuffer = (value) => value instanceof ArrayBuffer;
var isValidArray = (value) => Array.isArray(value);
var isValidObject = (value) => typeof value === "object" && value !== null;
var isValidOther = (value) => value != null;
function getTypeValidator(colType) {
  switch (colType) {
    case "string":
      return isValidString;
    case "bigint":
      return isValidBigint;
    case "boolean":
      return isValidBoolean;
    case "number":
      return isValidNumber;
    case "integer":
      return isValidInteger;
    case "date":
      return isValidDate;
    case "buffer":
      return isValidBuffer;
    case "array":
      return isValidArray;
    case "object":
      return isValidObject;
    case "other":
    default:
      return isValidOther;
  }
}
var DATE_TEST = /^(([-+]\d{2})?\d{4}(-\d{2}(-\d{2}))|(\d{1,2})\/(\d{1,2})\/(\d{2,4}))([T ]\d{2}:\d{2}(:\d{2}(\.\d{3})?)?(Z|[-+]\d{2}:\d{2})?)?$/;
function coerceToType(value, type) {
  switch (type) {
    case "string":
      return typeof value === "string" || value == null ? value : String(value);
    case "boolean":
      if (typeof value === "string") {
        const trimValue = value.trim().toLowerCase();
        return trimValue === "true" ? true : trimValue === "false" ? false : null;
      }
      return typeof value === "boolean" || value == null ? value : Boolean(value);
    case "bigint":
      return typeof value === "bigint" || value == null ? value : Number.isInteger(typeof value === "string" && !value.trim() ? NaN : +value) ? BigInt(value) : void 0;
    case "integer":
    // not a target type for coercion, but can be inferred
    case "number": {
      return typeof value === "number" ? value : value == null || typeof value === "string" && !value.trim() ? NaN : Number(value);
    }
    case "date": {
      if (value instanceof Date || value == null) return value;
      if (typeof value === "number") return new Date(value);
      const trimValue = String(value).trim();
      if (typeof value === "string" && !trimValue) return null;
      return new Date(DATE_TEST.test(trimValue) ? trimValue : NaN);
    }
    case "array":
    case "object":
    case "buffer":
    case "other":
      return value;
    default:
      throw new Error(`Unable to coerce to type: ${type}`);
  }
}
function getSchema(source) {
  const { columns } = source;
  let { schema } = source;
  if (!isQueryResultSetSchema(schema)) {
    schema = inferSchema(source, isQueryResultSetColumns(columns) ? columns : void 0);
    return { schema, inferred: true };
  }
  return { schema, inferred: false };
}
function applyTypes(source, operations) {
  const input3 = source;
  let { schema, inferred } = getSchema(source);
  const types2 = new Map(schema.map(({ name, type }) => [name, type]));
  if (operations.types) {
    for (const { name, type } of operations.types) {
      types2.set(name, type);
      if (schema === input3.schema) schema = schema.slice();
      const colIndex = schema.findIndex((col) => col.name === name);
      if (colIndex > -1) schema[colIndex] = { ...schema[colIndex], type };
    }
    source = source.map((d) => coerceRow(d, types2, schema));
  } else if (inferred) {
    source = source.map((d) => coerceRow(d, types2, schema));
  }
  return { source, schema };
}
function applyNames(source, operations) {
  if (!operations.names) return source;
  const overridesByName = new Map(operations.names.map((n) => [n.column, n]));
  return source.map(
    (d) => Object.fromEntries(Object.keys(d).map((k) => {
      const override = overridesByName.get(k);
      return [override?.name ?? k, d[k]];
    }))
  );
}
function __table(source, operations) {
  const errors = /* @__PURE__ */ new Map();
  const input3 = source;
  const typed = applyTypes(source, operations);
  source = typed.source;
  let schema = typed.schema;
  if (operations.derive) {
    const derivedSource = [];
    operations.derive.map(({ name, value }) => {
      let columnErrors = [];
      applyNames(source, operations).map((row, index) => {
        let resolved;
        try {
          resolved = value(row);
        } catch (error) {
          columnErrors.push({ index, error });
          resolved = void 0;
        }
        if (derivedSource[index]) {
          derivedSource[index] = { ...derivedSource[index], [name]: resolved };
        } else {
          derivedSource.push({ [name]: resolved });
        }
      });
      if (columnErrors.length) errors.set(name, columnErrors);
    });
    const typedDerived = applyTypes(derivedSource, operations);
    source = source.map((row, i) => ({ ...row, ...typedDerived.source[i] }));
    schema = [...schema, ...typedDerived.schema];
  }
  for (const { type, operands } of operations.filter) {
    const [{ value: column }] = operands;
    const values = operands.slice(1).map(({ value }) => value);
    switch (type) {
      // valid (matches the column type)
      case "v": {
        const [colType] = values;
        const isValid = getTypeValidator(colType);
        source = source.filter((d) => isValid(d[column]));
        break;
      }
      // not valid (doesn't match the column type)
      case "nv": {
        const [colType] = values;
        const isValid = getTypeValidator(colType);
        source = source.filter((d) => !isValid(d[column]));
        break;
      }
      case "eq": {
        const [value] = values;
        if (value instanceof Date) {
          const time = +value;
          source = source.filter((d) => +d[column] === time);
        } else {
          source = source.filter((d) => d[column] === value);
        }
        break;
      }
      case "ne": {
        const [value] = values;
        source = source.filter((d) => d[column] !== value);
        break;
      }
      case "c": {
        const [value] = values;
        source = source.filter(
          (d) => typeof d[column] === "string" && d[column].includes(value)
        );
        break;
      }
      case "nc": {
        const [value] = values;
        source = source.filter(
          (d) => typeof d[column] === "string" && !d[column].includes(value)
        );
        break;
      }
      case "in": {
        const set = new Set(values);
        source = source.filter((d) => set.has(d[column]));
        break;
      }
      case "nin": {
        const set = new Set(values);
        source = source.filter((d) => !set.has(d[column]));
        break;
      }
      case "n": {
        source = source.filter((d) => d[column] == null);
        break;
      }
      case "nn": {
        source = source.filter((d) => d[column] != null);
        break;
      }
      case "lt": {
        const [value] = values;
        source = source.filter((d) => d[column] < value);
        break;
      }
      case "lte": {
        const [value] = values;
        source = source.filter((d) => d[column] <= value);
        break;
      }
      case "gt": {
        const [value] = values;
        source = source.filter((d) => d[column] > value);
        break;
      }
      case "gte": {
        const [value] = values;
        source = source.filter((d) => d[column] >= value);
        break;
      }
      default:
        throw new Error(`unknown filter type: ${type}`);
    }
  }
  for (const { column, direction } of reverse(operations.sort)) {
    const compare = direction === "desc" ? descendingDefined : ascendingDefined;
    if (source === input3) source = source.slice();
    source.sort((a, b) => compare(a[column], b[column]));
  }
  let { from, to } = operations.slice;
  from = from == null ? 0 : Math.max(0, from);
  to = to == null ? Infinity : Math.max(0, to);
  if (from > 0 || to < Infinity) {
    source = source.slice(Math.max(0, from), Math.max(0, to));
  }
  let fullSchema = schema.slice();
  if (operations.select.columns) {
    if (schema) {
      const schemaByName = new Map(schema.map((s) => [s.name, s]));
      schema = operations.select.columns.map((c) => schemaByName.get(c));
    }
    source = source.map(
      (d) => Object.fromEntries(operations.select.columns.map((c) => [c, d[c]]))
    );
  }
  if (operations.names) {
    const overridesByName = new Map(operations.names.map((n) => [n.column, n]));
    if (schema) {
      schema = schema.map((s) => {
        const override = overridesByName.get(s.name);
        return { ...s, ...override ? { name: override.name } : null };
      });
    }
    if (fullSchema) {
      fullSchema = fullSchema.map((s) => {
        const override = overridesByName.get(s.name);
        return { ...s, ...override ? { name: override.name } : null };
      });
    }
    source = applyNames(source, operations);
  }
  if (source !== input3) {
    if (schema) source.schema = schema;
  }
  source.fullSchema = fullSchema;
  source.errors = errors;
  return source;
}
function coerceRow(object, types2, schema) {
  const coerced = {};
  for (const col of schema) {
    const type = types2.get(col.name);
    const value = object[col.name];
    coerced[col.name] = type === "raw" ? value : coerceToType(value, type);
  }
  return coerced;
}
function createTypeCount() {
  return {
    boolean: 0,
    integer: 0,
    number: 0,
    date: 0,
    string: 0,
    array: 0,
    object: 0,
    bigint: 0,
    buffer: 0,
    defined: 0
  };
}
var types = [
  "boolean",
  "integer",
  "number",
  "date",
  "bigint",
  "array",
  "object",
  "buffer"
  // Note: "other" and "string" are intentionally omitted; see below!
];
function getAllKeys(rows) {
  const keys = /* @__PURE__ */ new Set();
  for (const row of rows) {
    if (row) {
      for (const key in row) {
        if (Object.prototype.hasOwnProperty.call(row, key)) {
          keys.add(key);
        }
      }
    }
  }
  return Array.from(keys);
}
function inferSchema(source, columns = getAllKeys(source)) {
  const schema = [];
  const sampleSize = 100;
  const sample = source.slice(0, sampleSize);
  const typeCounts = {};
  for (const col of columns) {
    const colCount = typeCounts[col] = createTypeCount();
    for (const d of sample) {
      let value = d[col];
      if (value == null) continue;
      const type2 = typeof value;
      if (type2 !== "string") {
        ++colCount.defined;
        if (Array.isArray(value)) ++colCount.array;
        else if (value instanceof Date) ++colCount.date;
        else if (value instanceof ArrayBuffer) ++colCount.buffer;
        else if (type2 === "number") {
          ++colCount.number;
          if (Number.isInteger(value)) ++colCount.integer;
        } else if (type2 in colCount) ++colCount[type2];
      } else {
        value = value.trim();
        if (!value) continue;
        ++colCount.defined;
        ++colCount.string;
        if (/^(true|false)$/i.test(value)) {
          ++colCount.boolean;
        } else if (value && !isNaN(value)) {
          ++colCount.number;
          if (Number.isInteger(+value)) ++colCount.integer;
        } else if (DATE_TEST.test(value)) ++colCount.date;
      }
    }
    const minCount = Math.max(1, colCount.defined * 0.9);
    const type = greatest(
      types,
      (type2) => colCount[type2] >= minCount ? colCount[type2] : NaN
    ) ?? (colCount.string >= minCount ? "string" : "other");
    schema.push({
      name: col,
      type,
      inferred: type
    });
  }
  return schema;
}

// node_modules/@observablehq/stdlib/src/xlsx.js
var Workbook = class {
  constructor(workbook) {
    Object.defineProperties(this, {
      _: { value: workbook },
      sheetNames: {
        value: workbook.worksheets.map((s) => s.name),
        enumerable: true
      }
    });
  }
  sheet(name, options) {
    const sname = typeof name === "number" ? this.sheetNames[name] : this.sheetNames.includes(name += "") ? name : null;
    if (sname == null) throw new Error(`Sheet not found: ${name}`);
    const sheet = this._.getWorksheet(sname);
    return extract(sheet, options);
  }
};
function extract(sheet, { range: range3, headers } = {}) {
  let [[c0, r0], [c1, r1]] = parseRange(range3, sheet);
  const headerRow = headers ? sheet._rows[r0++] : null;
  let names = /* @__PURE__ */ new Set(["#"]);
  for (let n = c0; n <= c1; n++) {
    const value = headerRow ? valueOf(headerRow.findCell(n + 1)) : null;
    let name = value && value + "" || toColumn(n);
    while (names.has(name)) name += "_";
    names.add(name);
  }
  names = new Array(c0).concat(Array.from(names));
  const output = new Array(r1 - r0 + 1);
  for (let r = r0; r <= r1; r++) {
    const row = output[r - r0] = Object.create(null, { "#": { value: r + 1 } });
    const _row = sheet.getRow(r + 1);
    if (_row.hasValues)
      for (let c = c0; c <= c1; c++) {
        const value = valueOf(_row.findCell(c + 1));
        if (value != null) row[names[c + 1]] = value;
      }
  }
  output.columns = names.filter(() => true);
  return output;
}
function valueOf(cell) {
  if (!cell) return;
  const { value } = cell;
  if (value && typeof value === "object" && !(value instanceof Date)) {
    if (value.formula || value.sharedFormula) {
      return value.result && value.result.error ? NaN : value.result;
    }
    if (value.richText) {
      return richText(value);
    }
    if (value.text) {
      let { text: text4 } = value;
      if (text4.richText) text4 = richText(text4);
      return value.hyperlink && value.hyperlink !== text4 ? `${value.hyperlink} ${text4}` : text4;
    }
    return value;
  }
  return value;
}
function richText(value) {
  return value.richText.map((d) => d.text).join("");
}
function parseRange(specifier = ":", { columnCount, rowCount }) {
  specifier += "";
  if (!specifier.match(/^[A-Z]*\d*:[A-Z]*\d*$/))
    throw new Error("Malformed range specifier");
  const [[c0 = 0, r0 = 0], [c1 = columnCount - 1, r1 = rowCount - 1]] = specifier.split(":").map(fromCellReference);
  return [
    [c0, r0],
    [c1, r1]
  ];
}
function toColumn(c) {
  let sc = "";
  c++;
  do {
    sc = String.fromCharCode(64 + (c % 26 || 26)) + sc;
  } while (c = Math.floor((c - 1) / 26));
  return sc;
}
function fromCellReference(s) {
  const [, sc, sr] = s.match(/^([A-Z]*)(\d*)$/);
  let c = 0;
  if (sc)
    for (let i = 0; i < sc.length; i++)
      c += Math.pow(26, sc.length - i - 1) * (sc.charCodeAt(i) - 64);
  return [c ? c - 1 : void 0, sr ? +sr - 1 : void 0];
}

// node_modules/@observablehq/stdlib/src/fileAttachment.js
async function remote_fetch(file) {
  const response = await fetch(await file.url());
  if (!response.ok) throw new Error(`Unable to load file: ${file.name}`);
  return response;
}
function enforceSchema(source, schema) {
  const types2 = new Map(schema.map(({ name, type }) => [name, type]));
  return Object.assign(source.map((d) => coerceRow(d, types2, schema)), { schema });
}
async function dsv(file, delimiter, { array = false, typed = false } = {}) {
  const text4 = await file.text();
  const parse = delimiter === "	" ? array ? tsvParseRows : tsvParse : array ? csvParseRows : csvParse;
  if (typed === "auto" && !array) {
    const source = parse(text4);
    return enforceSchema(source, inferSchema(source, source.columns));
  }
  return parse(text4, typed && autoType);
}
var AbstractFile = class {
  constructor(name, mimeType) {
    Object.defineProperty(this, "name", { value: name, enumerable: true });
    if (mimeType !== void 0) Object.defineProperty(this, "mimeType", { value: mimeType + "", enumerable: true });
  }
  async blob() {
    return (await remote_fetch(this)).blob();
  }
  async arrayBuffer() {
    return (await remote_fetch(this)).arrayBuffer();
  }
  async text() {
    return (await remote_fetch(this)).text();
  }
  async json() {
    return (await remote_fetch(this)).json();
  }
  async stream() {
    return (await remote_fetch(this)).body;
  }
  async csv(options) {
    return dsv(this, ",", options);
  }
  async tsv(options) {
    return dsv(this, "	", options);
  }
  async image(props) {
    const url2 = await this.url();
    return new Promise((resolve2, reject) => {
      const i = new Image();
      if (new URL(url2, document.baseURI).origin !== new URL(location).origin) {
        i.crossOrigin = "anonymous";
      }
      Object.assign(i, props);
      i.onload = () => resolve2(i);
      i.onerror = () => reject(new Error(`Unable to load file: ${this.name}`));
      i.src = url2;
    });
  }
  async arrow({ version = 4 } = {}) {
    switch (version) {
      case 4: {
        const [Arrow, response] = await Promise.all([requireDefault(arrow4.resolve()), remote_fetch(this)]);
        return Arrow.Table.from(response);
      }
      case 9: {
        const [Arrow, response] = await Promise.all([import(`${cdn}${arrow9.resolve()}`), remote_fetch(this)]);
        return Arrow.tableFromIPC(response);
      }
      case 11: {
        const [Arrow, response] = await Promise.all([import(`${cdn}${arrow11.resolve()}`), remote_fetch(this)]);
        return Arrow.tableFromIPC(response);
      }
      default:
        throw new Error(`unsupported arrow version: ${version}`);
    }
  }
  async sqlite() {
    return SQLiteDatabaseClient.open(remote_fetch(this));
  }
  async zip() {
    const [JSZip, buffer2] = await Promise.all([requireDefault(jszip.resolve()), this.arrayBuffer()]);
    return new ZipArchive(await JSZip.loadAsync(buffer2));
  }
  async xml(mimeType = "application/xml") {
    return new DOMParser().parseFromString(await this.text(), mimeType);
  }
  async html() {
    return this.xml("text/html");
  }
  async xlsx() {
    const [ExcelJS, buffer2] = await Promise.all([requireDefault(exceljs.resolve()), this.arrayBuffer()]);
    return new Workbook(await new ExcelJS.Workbook().xlsx.load(buffer2));
  }
};
var FileAttachment = class extends AbstractFile {
  constructor(url2, name, mimeType) {
    super(name, mimeType);
    Object.defineProperty(this, "_url", { value: url2 });
  }
  async url() {
    return await this._url + "";
  }
};
function NoFileAttachments(name) {
  throw new Error(`File not found: ${name}`);
}
function FileAttachments(resolve2) {
  return Object.assign(
    (name) => {
      const result = resolve2(name += "");
      if (result == null) throw new Error(`File not found: ${name}`);
      if (typeof result === "object" && "url" in result) {
        const { url: url2, mimeType } = result;
        return new FileAttachment(url2, name, mimeType);
      }
      return new FileAttachment(result, name);
    },
    { prototype: FileAttachment.prototype }
    // instanceof
  );
}
var ZipArchive = class {
  constructor(archive) {
    Object.defineProperty(this, "_", { value: archive });
    this.filenames = Object.keys(archive.files).filter((name) => !archive.files[name].dir);
  }
  file(path) {
    const object = this._.file(path += "");
    if (!object || object.dir) throw new Error(`file not found: ${path}`);
    return new ZipArchiveEntry(object);
  }
};
var ZipArchiveEntry = class extends AbstractFile {
  constructor(object) {
    super(object.name);
    Object.defineProperty(this, "_", { value: object });
    Object.defineProperty(this, "_url", { writable: true });
  }
  async url() {
    return this._url || (this._url = this.blob().then(URL.createObjectURL));
  }
  async blob() {
    return this._.async("blob");
  }
  async arrayBuffer() {
    return this._.async("arraybuffer");
  }
  async text() {
    return this._.async("text");
  }
  async json() {
    return JSON.parse(await this.text());
  }
};

// node_modules/@observablehq/stdlib/src/dom/index.js
var dom_exports = {};
__export(dom_exports, {
  canvas: () => canvas,
  context2d: () => context2d,
  download: () => download,
  element: () => element2,
  input: () => input,
  range: () => range,
  select: () => select,
  svg: () => svg,
  text: () => text2,
  uid: () => uid
});

// node_modules/@observablehq/stdlib/src/dom/canvas.js
function canvas(width2, height) {
  var canvas2 = document.createElement("canvas");
  canvas2.width = width2;
  canvas2.height = height;
  return canvas2;
}

// node_modules/@observablehq/stdlib/src/dom/context2d.js
function context2d(width2, height, dpi) {
  if (dpi == null) dpi = devicePixelRatio;
  var canvas2 = document.createElement("canvas");
  canvas2.width = width2 * dpi;
  canvas2.height = height * dpi;
  canvas2.style.width = width2 + "px";
  var context = canvas2.getContext("2d");
  context.scale(dpi, dpi);
  return context;
}

// node_modules/@observablehq/stdlib/src/dom/download.js
function download(value, name = "untitled", label = "Save") {
  const a = document.createElement("a");
  const b = a.appendChild(document.createElement("button"));
  b.textContent = label;
  a.download = name;
  async function reset() {
    await new Promise(requestAnimationFrame);
    URL.revokeObjectURL(a.href);
    a.removeAttribute("href");
    b.textContent = label;
    b.disabled = false;
  }
  a.onclick = async (event) => {
    b.disabled = true;
    if (a.href) return reset();
    b.textContent = "Saving\u2026";
    try {
      const object = await (typeof value === "function" ? value() : value);
      b.textContent = "Download";
      a.href = URL.createObjectURL(object);
    } catch (ignore) {
      b.textContent = label;
    }
    if (event.eventPhase) return reset();
    b.disabled = false;
  };
  return a;
}

// node_modules/@observablehq/stdlib/src/dom/element.js
var namespaces = {
  math: "http://www.w3.org/1998/Math/MathML",
  svg: "http://www.w3.org/2000/svg",
  xhtml: "http://www.w3.org/1999/xhtml",
  xlink: "http://www.w3.org/1999/xlink",
  xml: "http://www.w3.org/XML/1998/namespace",
  xmlns: "http://www.w3.org/2000/xmlns/"
};
function element2(name, attributes) {
  var prefix = name += "", i = prefix.indexOf(":"), value;
  if (i >= 0 && (prefix = name.slice(0, i)) !== "xmlns") name = name.slice(i + 1);
  var element3 = namespaces.hasOwnProperty(prefix) ? document.createElementNS(namespaces[prefix], name) : document.createElement(name);
  if (attributes) for (var key in attributes) {
    prefix = key, i = prefix.indexOf(":"), value = attributes[key];
    if (i >= 0 && (prefix = key.slice(0, i)) !== "xmlns") key = key.slice(i + 1);
    if (namespaces.hasOwnProperty(prefix)) element3.setAttributeNS(namespaces[prefix], key, value);
    else element3.setAttribute(key, value);
  }
  return element3;
}

// node_modules/@observablehq/stdlib/src/dom/input.js
function input(type) {
  var input3 = document.createElement("input");
  if (type != null) input3.type = type;
  return input3;
}

// node_modules/@observablehq/stdlib/src/dom/range.js
function range(min, max, step) {
  if (arguments.length === 1) max = min, min = null;
  var input3 = document.createElement("input");
  input3.min = min = min == null ? 0 : +min;
  input3.max = max = max == null ? 1 : +max;
  input3.step = step == null ? "any" : step = +step;
  input3.type = "range";
  return input3;
}

// node_modules/@observablehq/stdlib/src/dom/select.js
function select(values) {
  var select2 = document.createElement("select");
  Array.prototype.forEach.call(values, function(value) {
    var option = document.createElement("option");
    option.value = option.textContent = value;
    select2.appendChild(option);
  });
  return select2;
}

// node_modules/@observablehq/stdlib/src/dom/svg.js
function svg(width2, height) {
  var svg3 = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  svg3.setAttribute("viewBox", [0, 0, width2, height]);
  svg3.setAttribute("width", width2);
  svg3.setAttribute("height", height);
  return svg3;
}

// node_modules/@observablehq/stdlib/src/dom/text.js
function text2(value) {
  return document.createTextNode(value);
}

// node_modules/@observablehq/stdlib/src/dom/uid.js
var count = 0;
function uid(name) {
  return new Id("O-" + (name == null ? "" : name + "-") + ++count);
}
function Id(id) {
  this.id = id;
  this.href = new URL(`#${id}`, location) + "";
}
Id.prototype.toString = function() {
  return "url(" + this.href + ")";
};

// node_modules/@observablehq/stdlib/src/files/index.js
var files_exports = {};
__export(files_exports, {
  buffer: () => buffer,
  text: () => text3,
  url: () => url
});

// node_modules/@observablehq/stdlib/src/files/buffer.js
function buffer(file) {
  return new Promise(function(resolve2, reject) {
    var reader = new FileReader();
    reader.onload = function() {
      resolve2(reader.result);
    };
    reader.onerror = reject;
    reader.readAsArrayBuffer(file);
  });
}

// node_modules/@observablehq/stdlib/src/files/text.js
function text3(file) {
  return new Promise(function(resolve2, reject) {
    var reader = new FileReader();
    reader.onload = function() {
      resolve2(reader.result);
    };
    reader.onerror = reject;
    reader.readAsText(file);
  });
}

// node_modules/@observablehq/stdlib/src/files/url.js
function url(file) {
  return new Promise(function(resolve2, reject) {
    var reader = new FileReader();
    reader.onload = function() {
      resolve2(reader.result);
    };
    reader.onerror = reject;
    reader.readAsDataURL(file);
  });
}

// node_modules/@observablehq/stdlib/src/generators/index.js
var generators_exports = {};
__export(generators_exports, {
  disposable: () => disposable,
  filter: () => filter,
  input: () => input2,
  map: () => map2,
  observe: () => observe,
  queue: () => queue2,
  range: () => range2,
  valueAt: () => valueAt,
  worker: () => worker
});

// node_modules/@observablehq/stdlib/src/that.js
function that() {
  return this;
}

// node_modules/@observablehq/stdlib/src/generators/disposable.js
function disposable(value, dispose) {
  let done = false;
  if (typeof dispose !== "function") {
    throw new Error("dispose is not a function");
  }
  return {
    [Symbol.iterator]: that,
    next: () => done ? { done: true } : (done = true, { done: false, value }),
    return: () => (done = true, dispose(value), { done: true }),
    throw: () => ({ done: done = true })
  };
}

// node_modules/@observablehq/stdlib/src/generators/filter.js
function* filter(iterator, test) {
  var result, index = -1;
  while (!(result = iterator.next()).done) {
    if (test(result.value, ++index)) {
      yield result.value;
    }
  }
}

// node_modules/@observablehq/stdlib/src/generators/observe.js
function observe(initialize) {
  let stale = false;
  let value;
  let resolve2;
  const dispose = initialize(change);
  if (dispose != null && typeof dispose !== "function") {
    throw new Error(typeof dispose.then === "function" ? "async initializers are not supported" : "initializer returned something, but not a dispose function");
  }
  function change(x) {
    if (resolve2) resolve2(x), resolve2 = null;
    else stale = true;
    return value = x;
  }
  function next() {
    return { done: false, value: stale ? (stale = false, Promise.resolve(value)) : new Promise((_) => resolve2 = _) };
  }
  return {
    [Symbol.iterator]: that,
    throw: () => ({ done: true }),
    return: () => (dispose != null && dispose(), { done: true }),
    next
  };
}

// node_modules/@observablehq/stdlib/src/generators/input.js
function input2(input3) {
  return observe(function(change) {
    var event = eventof(input3), value = valueof(input3);
    function inputted() {
      change(valueof(input3));
    }
    input3.addEventListener(event, inputted);
    if (value !== void 0) change(value);
    return function() {
      input3.removeEventListener(event, inputted);
    };
  });
}
function valueof(input3) {
  switch (input3.type) {
    case "range":
    case "number":
      return input3.valueAsNumber;
    case "date":
      return input3.valueAsDate;
    case "checkbox":
      return input3.checked;
    case "file":
      return input3.multiple ? input3.files : input3.files[0];
    case "select-multiple":
      return Array.from(input3.selectedOptions, (o) => o.value);
    default:
      return input3.value;
  }
}
function eventof(input3) {
  switch (input3.type) {
    case "button":
    case "submit":
    case "checkbox":
      return "click";
    case "file":
      return "change";
    default:
      return "input";
  }
}

// node_modules/@observablehq/stdlib/src/generators/map.js
function* map2(iterator, transform) {
  var result, index = -1;
  while (!(result = iterator.next()).done) {
    yield transform(result.value, ++index);
  }
}

// node_modules/@observablehq/stdlib/src/generators/queue.js
function queue2(initialize) {
  let resolve2;
  const queue3 = [];
  const dispose = initialize(push);
  if (dispose != null && typeof dispose !== "function") {
    throw new Error(typeof dispose.then === "function" ? "async initializers are not supported" : "initializer returned something, but not a dispose function");
  }
  function push(x) {
    queue3.push(x);
    if (resolve2) resolve2(queue3.shift()), resolve2 = null;
    return x;
  }
  function next() {
    return { done: false, value: queue3.length ? Promise.resolve(queue3.shift()) : new Promise((_) => resolve2 = _) };
  }
  return {
    [Symbol.iterator]: that,
    throw: () => ({ done: true }),
    return: () => (dispose != null && dispose(), { done: true }),
    next
  };
}

// node_modules/@observablehq/stdlib/src/generators/range.js
function* range2(start, stop, step) {
  start = +start;
  stop = +stop;
  step = (n = arguments.length) < 2 ? (stop = start, start = 0, 1) : n < 3 ? 1 : +step;
  var i = -1, n = Math.max(0, Math.ceil((stop - start) / step)) | 0;
  while (++i < n) {
    yield start + i * step;
  }
}

// node_modules/@observablehq/stdlib/src/generators/valueAt.js
function valueAt(iterator, i) {
  if (!isFinite(i = +i) || i < 0 || i !== i | 0) return;
  var result, index = -1;
  while (!(result = iterator.next()).done) {
    if (++index === i) {
      return result.value;
    }
  }
}

// node_modules/@observablehq/stdlib/src/generators/worker.js
function worker(source) {
  const url2 = URL.createObjectURL(new Blob([source], { type: "text/javascript" }));
  const worker2 = new Worker(url2);
  return disposable(worker2, () => {
    worker2.terminate();
    URL.revokeObjectURL(url2);
  });
}

// node_modules/@observablehq/stdlib/src/template.js
function template(render, wrapper) {
  return function(strings) {
    var string = strings[0], parts = [], part, root = null, node, nodes, walker, i, n, j, m, k = -1;
    for (i = 1, n = arguments.length; i < n; ++i) {
      part = arguments[i];
      if (part instanceof Node) {
        parts[++k] = part;
        string += "<!--o:" + k + "-->";
      } else if (Array.isArray(part)) {
        for (j = 0, m = part.length; j < m; ++j) {
          node = part[j];
          if (node instanceof Node) {
            if (root === null) {
              parts[++k] = root = document.createDocumentFragment();
              string += "<!--o:" + k + "-->";
            }
            root.appendChild(node);
          } else {
            root = null;
            string += node;
          }
        }
        root = null;
      } else {
        string += part;
      }
      string += strings[i];
    }
    root = render(string);
    if (++k > 0) {
      nodes = new Array(k);
      walker = document.createTreeWalker(root, NodeFilter.SHOW_COMMENT, null, false);
      while (walker.nextNode()) {
        node = walker.currentNode;
        if (/^o:/.test(node.nodeValue)) {
          nodes[+node.nodeValue.slice(2)] = node;
        }
      }
      for (i = 0; i < k; ++i) {
        if (node = nodes[i]) {
          node.parentNode.replaceChild(parts[i], node);
        }
      }
    }
    return root.childNodes.length === 1 ? root.removeChild(root.firstChild) : root.nodeType === 11 ? ((node = wrapper()).appendChild(root), node) : root;
  };
}

// node_modules/@observablehq/stdlib/src/html.js
var html = template(function(string) {
  var template2 = document.createElement("template");
  template2.innerHTML = string.trim();
  return document.importNode(template2.content, true);
}, function() {
  return document.createElement("span");
});

// node_modules/@observablehq/stdlib/src/leaflet.js
async function leaflet2(require3) {
  const L = await require3(leaflet.resolve());
  if (!L._style) {
    const link = document.createElement("link");
    link.rel = "stylesheet";
    link.href = await require3.resolve(leaflet.resolve("dist/leaflet.css"));
    L._style = document.head.appendChild(link);
  }
  return L;
}

// node_modules/@observablehq/stdlib/src/md.js
function md(require3) {
  return require3(marked.resolve()).then(function(marked2) {
    return template(
      function(string) {
        var root = document.createElement("div");
        root.innerHTML = marked2(string, { langPrefix: "" }).trim();
        var code = root.querySelectorAll("pre code[class]");
        if (code.length > 0) {
          require3(highlight.resolve()).then(function(hl) {
            code.forEach(function(block) {
              function done() {
                hl.highlightBlock(block);
                block.parentNode.classList.add("observablehq--md-pre");
              }
              if (hl.getLanguage(block.className)) {
                done();
              } else {
                require3(highlight.resolve("async-languages/index.js")).then((index) => {
                  if (index.has(block.className)) {
                    return require3(highlight.resolve("async-languages/" + index.get(block.className))).then((language) => {
                      hl.registerLanguage(block.className, language);
                    });
                  }
                }).then(done, done);
              }
            });
          });
        }
        return root;
      },
      function() {
        return document.createElement("div");
      }
    );
  });
}

// node_modules/@observablehq/stdlib/src/mermaid.js
async function mermaid2(require3) {
  const mer = await require3(mermaid.resolve());
  mer.initialize({ securityLevel: "loose", theme: "neutral" });
  return function mermaid3() {
    const root = document.createElement("div");
    root.innerHTML = mer.render(uid().id, String.raw.apply(String, arguments));
    return root.removeChild(root.firstChild);
  };
}

// node_modules/@observablehq/stdlib/src/mutable.js
function Mutable(value) {
  let change;
  Object.defineProperties(this, {
    generator: { value: observe((_) => void (change = _)) },
    value: { get: () => value, set: (x) => change(value = x) }
    // eslint-disable-line no-setter-return
  });
  if (value !== void 0) change(value);
}

// node_modules/@observablehq/stdlib/src/now.js
function* now() {
  while (true) {
    yield Date.now();
  }
}

// node_modules/@observablehq/stdlib/src/promises/index.js
var promises_exports = {};
__export(promises_exports, {
  delay: () => delay,
  tick: () => tick,
  when: () => when
});

// node_modules/@observablehq/stdlib/src/promises/delay.js
function delay(duration, value) {
  return new Promise(function(resolve2) {
    setTimeout(function() {
      resolve2(value);
    }, duration);
  });
}

// node_modules/@observablehq/stdlib/src/promises/when.js
var timeouts = /* @__PURE__ */ new Map();
function timeout(now2, time) {
  var t = new Promise(function(resolve2) {
    timeouts.delete(time);
    var delay2 = time - now2;
    if (!(delay2 > 0)) throw new Error("invalid time");
    if (delay2 > 2147483647) throw new Error("too long to wait");
    setTimeout(resolve2, delay2);
  });
  timeouts.set(time, t);
  return t;
}
function when(time, value) {
  var now2;
  return (now2 = timeouts.get(time = +time)) ? now2.then(() => value) : (now2 = Date.now()) >= time ? Promise.resolve(value) : timeout(now2, time).then(() => value);
}

// node_modules/@observablehq/stdlib/src/promises/tick.js
function tick(duration, value) {
  return when(Math.ceil((Date.now() + 1) / duration) * duration, value);
}

// node_modules/@observablehq/stdlib/src/resolve.js
function resolve(name, base) {
  if (/^(\w+:)|\/\//i.test(name)) return name;
  if (/^[.]{0,2}\//i.test(name)) return new URL(name, base == null ? location : base).href;
  if (!name.length || /^[\s._]/.test(name) || /\s$/.test(name)) throw new Error("illegal name");
  return "https://unpkg.com/" + name;
}

// node_modules/@observablehq/stdlib/src/svg.js
var svg2 = template(function(string) {
  var root = document.createElementNS("http://www.w3.org/2000/svg", "g");
  root.innerHTML = string.trim();
  return root;
}, function() {
  return document.createElementNS("http://www.w3.org/2000/svg", "g");
});

// node_modules/@observablehq/stdlib/src/tex.js
var raw = String.raw;
function style(href) {
  return new Promise(function(resolve2, reject) {
    var link = document.createElement("link");
    link.rel = "stylesheet";
    link.href = href;
    link.onerror = reject;
    link.onload = resolve2;
    document.head.appendChild(link);
  });
}
function tex(require3) {
  return Promise.all([
    require3(katex.resolve()),
    require3.resolve(katex.resolve("dist/katex.min.css")).then(style)
  ]).then(function(values) {
    var katex2 = values[0], tex2 = renderer();
    function renderer(options) {
      return function() {
        var root = document.createElement("div");
        katex2.render(raw.apply(String, arguments), root, options);
        return root.removeChild(root.firstChild);
      };
    }
    tex2.options = renderer;
    tex2.block = renderer({ displayMode: true });
    return tex2;
  });
}

// node_modules/@observablehq/stdlib/src/vegalite.js
async function vl(require3) {
  const [v, vl2, api] = await Promise.all([vega, vegalite, vegaliteApi].map((d) => require3(d.resolve())));
  return api.register(v, vl2);
}

// node_modules/@observablehq/stdlib/src/width.js
function width() {
  return observe(function(change) {
    var width2 = change(document.body.clientWidth);
    function resized() {
      var w = document.body.clientWidth;
      if (w !== width2) change(width2 = w);
    }
    window.addEventListener("resize", resized);
    return function() {
      window.removeEventListener("resize", resized);
    };
  });
}

// node_modules/@observablehq/stdlib/src/library.js
var Library = Object.assign(Object.defineProperties(function Library2(resolver) {
  const require3 = requirer(resolver);
  Object.defineProperties(this, properties({
    FileAttachment: () => NoFileAttachments,
    Mutable: () => Mutable,
    now,
    width,
    // Tagged template literals
    dot: () => require3(graphviz.resolve()),
    htl: () => require3(htl.resolve()),
    html: () => html,
    md: () => md(require3),
    svg: () => svg2,
    tex: () => tex(require3),
    // Recommended libraries
    // https://observablehq.com/@observablehq/recommended-libraries
    _: () => require3(lodash.resolve()),
    aq: () => require3.alias({ "apache-arrow": arrow4.resolve() })(arquero.resolve()),
    // TODO upgrade to apache-arrow@9
    Arrow: () => require3(arrow4.resolve()),
    // TODO upgrade to apache-arrow@9
    d3: () => require3(d3.resolve()),
    DuckDBClient: () => DuckDBClient,
    Inputs: () => require3(inputs.resolve()).then((Inputs) => ({ ...Inputs, file: Inputs.fileOf(AbstractFile) })),
    L: () => leaflet2(require3),
    mermaid: () => mermaid2(require3),
    Plot: () => require3(plot.resolve()),
    __query: () => __query,
    require: () => require3,
    resolve: () => resolve,
    // deprecated; use async require.resolve instead
    SQLite: () => SQLite(require3),
    SQLiteDatabaseClient: () => SQLiteDatabaseClient,
    topojson: () => require3(topojson.resolve()),
    vl: () => vl(require3),
    // Sample datasets
    // https://observablehq.com/@observablehq/sample-datasets
    aapl: () => new FileAttachment("https://static.observableusercontent.com/files/3ccff97fd2d93da734e76829b2b066eafdaac6a1fafdec0faf6ebc443271cfc109d29e80dd217468fcb2aff1e6bffdc73f356cc48feb657f35378e6abbbb63b9").csv({ typed: true }),
    alphabet: () => new FileAttachment("https://static.observableusercontent.com/files/75d52e6c3130b1cae83cda89305e17b50f33e7420ef205587a135e8562bcfd22e483cf4fa2fb5df6dff66f9c5d19740be1cfaf47406286e2eb6574b49ffc685d").csv({ typed: true }),
    cars: () => new FileAttachment("https://static.observableusercontent.com/files/048ec3dfd528110c0665dfa363dd28bc516ffb7247231f3ab25005036717f5c4c232a5efc7bb74bc03037155cb72b1abe85a33d86eb9f1a336196030443be4f6").csv({ typed: true }),
    citywages: () => new FileAttachment("https://static.observableusercontent.com/files/39837ec5121fcc163131dbc2fe8c1a2e0b3423a5d1e96b5ce371e2ac2e20a290d78b71a4fb08b9fa6a0107776e17fb78af313b8ea70f4cc6648fad68ddf06f7a").csv({ typed: true }),
    diamonds: () => new FileAttachment("https://static.observableusercontent.com/files/87942b1f5d061a21fa4bb8f2162db44e3ef0f7391301f867ab5ba718b225a63091af20675f0bfe7f922db097b217b377135203a7eab34651e21a8d09f4e37252").csv({ typed: true }),
    flare: () => new FileAttachment("https://static.observableusercontent.com/files/a6b0d94a7f5828fd133765a934f4c9746d2010e2f342d335923991f31b14120de96b5cb4f160d509d8dc627f0107d7f5b5070d2516f01e4c862b5b4867533000").csv({ typed: true }),
    industries: () => new FileAttachment("https://static.observableusercontent.com/files/76f13741128340cc88798c0a0b7fa5a2df8370f57554000774ab8ee9ae785ffa2903010cad670d4939af3e9c17e5e18e7e05ed2b38b848ac2fc1a0066aa0005f").csv({ typed: true }),
    miserables: () => new FileAttachment("https://static.observableusercontent.com/files/31d904f6e21d42d4963ece9c8cc4fbd75efcbdc404bf511bc79906f0a1be68b5a01e935f65123670ed04e35ca8cae3c2b943f82bf8db49c5a67c85cbb58db052").json(),
    olympians: () => new FileAttachment("https://static.observableusercontent.com/files/31ca24545a0603dce099d10ee89ee5ae72d29fa55e8fc7c9ffb5ded87ac83060d80f1d9e21f4ae8eb04c1e8940b7287d179fe8060d887fb1f055f430e210007c").csv({ typed: true }),
    penguins: () => new FileAttachment("https://static.observableusercontent.com/files/715db1223e067f00500780077febc6cebbdd90c151d3d78317c802732252052ab0e367039872ab9c77d6ef99e5f55a0724b35ddc898a1c99cb14c31a379af80a").csv({ typed: true }),
    pizza: () => new FileAttachment("https://static.observableusercontent.com/files/c653108ab176088cacbb338eaf2344c4f5781681702bd6afb55697a3f91b511c6686ff469f3e3a27c75400001a2334dbd39a4499fe46b50a8b3c278b7d2f7fb5").csv({ typed: true }),
    weather: () => new FileAttachment("https://static.observableusercontent.com/files/693a46b22b33db0f042728700e0c73e836fa13d55446df89120682d55339c6db7cc9e574d3d73f24ecc9bc7eb9ac9a1e7e104a1ee52c00aab1e77eb102913c1f").csv({ typed: true }),
    // Note: these are namespace objects, and thus exposed directly rather than
    // being wrapped in a function. This allows library.Generators to resolve,
    // rather than needing module.value.
    DOM: dom_exports,
    Files: files_exports,
    Generators: generators_exports,
    Promises: promises_exports
  }));
}, {
  resolve: {
    get: () => requireDefault.resolve,
    enumerable: true,
    configurable: true
  },
  require: {
    get: () => requireDefault,
    set: setDefaultRequire,
    enumerable: true,
    configurable: true
  }
}), {
  resolveFrom,
  requireFrom
});
function properties(values) {
  return Object.fromEntries(Object.entries(values).map(property));
}
function property([key, value]) {
  return [key, { value, writable: true, enumerable: true }];
}
export {
  AbstractFile,
  FileAttachments,
  Library,
  __table as applyDataTableOperations,
  arrayIsPrimitive,
  getArrowTableSchema,
  getSchema,
  getTypeValidator,
  inferSchema,
  isArqueroTable,
  isArrowTable,
  isDataArray,
  isDatabaseClient,
  loadDataSource,
  makeQueryTemplate,
  observe
};
