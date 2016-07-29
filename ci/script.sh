if [ "${TRAVIS_RUST_VERSION}" != "nightly" ]; then
    export FEATURES="--features stable"
fi

cargo build $FEATURES
cd easy-plugin-tests
RUST_BACKTRACE=1 cargo test $FEATURES --verbose -- --nocapture
