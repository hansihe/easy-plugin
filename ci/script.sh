set -e

if [ "${TRAVIS_RUST_VERSION}" != "nightly" ]; then
    export FEATURES="--features stable"
fi

pushd parsers
RUST_BACKTRACE=1 cargo test $FEATURES --verbose -- --nocapture
popd

cargo build $FEATURES

pushd easy-plugin-tests
RUST_BACKTRACE=1 cargo test $FEATURES --verbose -- --nocapture
popd
