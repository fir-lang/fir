if [ "$#" -gt 0 ]; then
    files=("$@")
else
    files=()
    for f in **/*.fir; do
        skip=false
        for skip_f in "${skip_files[@]}"; do
            if [[ "$f" == "$skip_f" ]]; then
                skip=true
                break
            fi
        done

        if ! $skip; then
            files+=("$f")
        fi
    done
fi
