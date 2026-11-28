# Both tools take names relative to the proto import root.
set -eu
proto_dir=$1
shift

googleapis=${GOOGLEAPIS_DIR:-}
if [ -z "$googleapis" ]; then
    buf_cache=${BUF_CACHE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/buf}
    for dir in "$buf_cache"/v3/modules/b5/buf.build/googleapis/googleapis/*/files; do
        if [ -f "$dir/google/api/annotations.proto" ]; then
            googleapis=$dir
            break
        fi
    done
fi
if [ -z "$googleapis" ] || [ ! -f "$googleapis/google/api/annotations.proto" ]; then
    echo 'Set GOOGLEAPIS_DIR to a googleapis checkout containing google/api/annotations.proto.' >&2
    exit 2
fi

googleapis=$(cd "$googleapis" && pwd)
tool_path() {
    case "$1" in
        /*) printf '%s\n' "$1" ;;
        */*) printf '%s/%s\n' "$PWD" "$1" ;;
        *) printf '%s\n' "$1" ;;
    esac
}
protoc=$(tool_path "${PROTOC:-protoc}")
api_linter=$(tool_path "${API_LINTER:-api-linter}")
if [ -n "${PROTOBUF_INCLUDE:-}" ]; then
    protobuf=$(cd "$PROTOBUF_INCLUDE" && pwd)
    set -- -I "$protobuf" "$@"
fi
set -- -I . -I "$googleapis" "$@"
cd "$proto_dir"
"$protoc" --descriptor_set_out=/dev/null "$@"
"$api_linter" --set-exit-status --output-format=summary "$@"
