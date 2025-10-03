# see https://rocq-prover.org/docs/opam-packaging for how to update this:


## Tag a version

```bash
git tag 1.0.0
git push origin 1.0.0
```

If your repository is on GitHub at $YOU/foo (where $YOU is your GitHub
user name), the archive corresponding to the tag 1.0.0 can be
downloaded from this URL:
https://github.com/$YOU/foo/archive/1.0.0.tar.gz, using `curl -L` or
your browser for example.

## checksum

You can then record its checksum which will be used in the package
definition using:

```bash
YOURHASH=`shasum -a 512 1.0.0.tar.gz`
```

## upload (?)

Finally, you must upload the archive on GitHub as an asset of your release (using Edit Release). This is necessary as GitHub does not guarantee the checksum stability of auto-generated /archive/ tarballs. One can also use the gh CLI tool to upload an archive to a release (gh release upload tag archive.tar.gz). Your release will then have an url of shape:

https://github.com/$YOU/foo/releases/download/1.0.0/1.0.0.tar.gz

## update the rocq repository opam archive 

## fork it  if not alerady done

### Clone it

This creates a clone with two remotes, one for the official archive,
called upstream, and one for your fork, called origin.

``` bash
git clone https://github.com/rocq-prover/opam -o upstream
```

## add your fork as a remote

``` bash
cd opam
git remote add origin https://github.com/$YOU/opam
```

## create a branch

``` bash
git checkout -b rocq-foo.1.0.0 upstream/master
```

# Create a new directory for the new version

In the rocq-prover/opam directory, create a sub-directory named as follows:

``` bash
mkdir -p released/packages/rocq-foo/rocq-foo.1.0.0
```

# add a opam file in this diorectory


Template below:

when updating an existing one: 

- update url/src
- update url/checksum
- update dates
- update dependencies with coq versions and other package versions (Ltac2?)
- check the `build`, `install` and `test` commands

``` bash
opam-version: "2.0"
synopsis: "A Rocq library doing wonders" # One-line description
description: """
  Foo does bar with baz.
""" # Longer description, can span several lines

homepage: "https://github.com/$YOU/foo"
dev-repo: "git+https://github.com/$YOU/foo.git"
bug-reports: "https://github.com/$YOU/foo/issues"
doc: "https://$YOU.github.io/foo/"
maintainer: "your@email.address"
authors: [
  "You"
]
license: "MIT" # Make sure this is reflected by a LICENSE file in your sources

depends: [
  "rocq-core" {>= "9.0" & < "9.1~"}
  "rocq-stdlib" {>= "9.0" & < "9.1~"} # If necessary
]

build: [
  [make "-j%{jobs}%"]
]

install: [
  [make "install"]
]

run-test: [
  ["./configure.sh"]
  [make lib "-j%{jobs}%"]
  [make tests ]
]

url {
  src: "https://github.com/$YOU/foo/releases/download/1.0.0/1.0.0.tar.gz"
  checksum: "sha512=$YOURHASH"
}

tags: [
  "keyword:fooish"
  "category:Miscellaneous/Rocq Extensions"
  "date:2025-07-01"
  "logpath:Foo"
]
```

# Commit the opam file

git add released/packages/rocq-foo/rocq-foo.1.0.0/opam
git commit -m 'Package rocq-foo.1.0.0'

# call the linter

opam lint --check-upstream released/packages/rocq-foo/rocq-foo.1.0.0/opam
