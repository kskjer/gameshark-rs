import * as wasm from "gsopt-web";

(function() {
    var [input, output, details, button] = ['gs-input', 'gs-output', 'gs-details', 'gs-button']
        .map(x => document.getElementById(x));

    button.addEventListener('click', () => {
        var result = wasm.crush_code(input.value);

        output.value = result.get_compressed();
        details.innerText = result.get_details();
    })
})();

