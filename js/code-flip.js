document.addEventListener('DOMContentLoaded', () => {
    document.querySelectorAll('.theorem-proof').forEach(proof => {
        const inner = proof.querySelector('.proof-flip-inner');
        const button = proof.querySelector('.flip-btn');
        if (!inner || !button) return;

        button.addEventListener('click', () => {
            const flipped = inner.classList.toggle('flipped');
            button.innerHTML = flipped
                ? '<i class="codicon codicon-file-symlink-file"></i>'
                : '<i class="codicon codicon-file-code"></i>';
            button.title = flipped ? '返回证明' : '查看 Lean 源码';
        });
    });
});
