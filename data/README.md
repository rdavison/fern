# Corpus data

## `mr.txt` (not committed)

"Monkeyracer": the AKL community's concatenation of the quotes from Typeracer and Monkeytype, one
quote per line. The quotes belong to their authors, so the text itself is not redistributed here and
`data/*.txt` is ignored by git. To reproduce the tables, place the file at `data/mr.txt` and check it:

| Property | Value |
|---|---|
| SHA-256 | `6fee92e8b4ff0e3eaedb813ce36e8d0f91d7e893126188b7f32c8c93c31aead9` |
| Size | 2,294,644 bytes, UTF-8 |
| Lines | 18,053 |

## Derived tables (committed)

Each is a 900-entry TSV: one line per ordered key pair, with `#` comment lines at the top.

| File | Counts | Total |
|---|---|---|
| `mr.tsv` | bigrams: adjacent keys, both mapped | 1,425,006 |
| `mr-spacegrams.tsv` | key, space, key (the outer pair) | 405,924 |
| `mr-skipgrams.tsv` | key, key, key (the outer pair) | 1,020,952 |

How the text is read:

- **Keys:** the letters `a`–`z` and `, . ' ;`. ASCII capitals are folded to lower case.
- **Unmapped characters:** everything else, including digits, `-`, `?`, `"`, the typographic
  apostrophe `’`, the space and the newline. An unmapped character breaks the stream, so no bigram
  spans it.
- **Spacegrams:** only a literal space counts as the middle of a spacegram. A newline never joins
  two quotes.

The tables were produced with the commands below. `check` compares all 900 entries against the
text through `Fern.Solver.countLines`, which is proved equal to the text's bigram counts. An
independent Python count agreed exactly on bigrams and spacegrams.

```
fern-solve count data/mr.txt > data/mr.tsv
fern-solve count --spacegrams data/mr.txt > data/mr-spacegrams.tsv
fern-solve count --skipgrams data/mr.txt > data/mr-skipgrams.tsv
fern-solve check data/mr.txt data/mr.tsv
```

`mr.result` is the output of `fern-solve solve data/mr.tsv`.
