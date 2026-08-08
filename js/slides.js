/**
 * Slides Framework — 演示文稿导航引擎
 *
 * 功能：
 *   - iframe 加载独立 HTML 幻灯片
 *   - 悬浮按钮导航（上一页 / 下一页）
 *   - 键盘快捷键：← → ↑ ↓ Home End F Enter Space
 *   - 触摸滑动支持
 *   - URL hash 直链（#3 跳到第 3 页）
 *   - 空闲自动淡出按钮
 */

(function () {
    "use strict";

    // ── DOM 引用 ──
    const frame       = document.getElementById("slide-frame");
    const counter     = document.getElementById("slide-counter");
    const btnPrev     = document.getElementById("btn-prev");
    const btnNext     = document.getElementById("btn-next");
    const btnFull     = document.getElementById("btn-fullscreen");

    // ── 状态 ──
    const total = SLIDES.length;
    let current = 0;              // 0-indexed
    let idleTimer = null;
    const IDLE_DELAY = 3000;      // 3 秒不动就算 idle

    // ── 工具函数 ──
    function getSlideFile(index) {
        const s = SLIDES[index];
        return typeof s === "string" ? s : s.file;
    }

    function getSlideTitle(index) {
        const s = SLIDES[index];
        if (typeof s === "string") return "";
        return s.title || "";
    }

    // ── 更新 UI ──
    function updateCounter() {
        const t = getSlideTitle(current);
        const text = t
            ? `${current + 1} / ${total}  ·  ${t}`
            : `${current + 1} / ${total}`;
        counter.textContent = text;
    }

    function updateButtons() {
        btnPrev.disabled = (current === 0);
        btnNext.disabled = (current === total - 1);
    }

    // ── 闲置淡出 ──
    function resetIdle() {
        btnPrev.classList.remove("idle");
        btnNext.classList.remove("idle");
        btnFull.classList.remove("idle");
        counter.classList.remove("hidden");
        clearTimeout(idleTimer);
        idleTimer = setTimeout(() => {
            btnPrev.classList.add("idle");
            btnNext.classList.add("idle");
            btnFull.classList.add("idle");
            counter.classList.add("hidden");
        }, IDLE_DELAY);
    }

    // ── 导航核心 ──
    function navigateTo(index) {
        if (index < 0 || index >= total) return;

        current = index;
        frame.src = getSlideFile(current);

        updateCounter();
        updateButtons();
        resetIdle();

        // 更新 URL hash
        if (window.location.hash !== "#" + (current + 1)) {
            history.replaceState(null, "", "#" + (current + 1));
        }
    }

    function goNext() {
        if (current < total - 1) navigateTo(current + 1);
    }

    function goPrev() {
        if (current > 0) navigateTo(current - 1);
    }

    // ── 按钮事件 ──
    btnPrev.addEventListener("click", goPrev);
    btnNext.addEventListener("click", goNext);
    btnFull.addEventListener("click", () => {
        if (document.fullscreenElement) {
            document.exitFullscreen();
        } else {
            document.documentElement.requestFullscreen();
        }
    });

    // ── 键盘事件 ──
    document.addEventListener("keydown", (e) => {
        if (e.target.tagName === "INPUT" || e.target.tagName === "TEXTAREA" || e.target.isContentEditable) {
            return;
        }

        switch (e.key) {
            case "ArrowRight":
            case "ArrowDown":
            case " ":              // 空格
            case "Enter":          // 回车
                e.preventDefault();
                goNext();
                break;
            case "ArrowLeft":
            case "ArrowUp":
                e.preventDefault();
                goPrev();
                break;
            case "Home":
                e.preventDefault();
                navigateTo(0);
                break;
            case "End":
                e.preventDefault();
                navigateTo(total - 1);
                break;
            case "f":
            case "F":
                if (!e.ctrlKey && !e.metaKey) {
                    e.preventDefault();
                    if (document.fullscreenElement) {
                        document.exitFullscreen();
                    } else {
                        document.documentElement.requestFullscreen();
                    }
                }
                break;
        }
    });

    // ── 触摸滑动 ──
    (function () {
        let touchStartX = 0;
        let touchStartY = 0;

        document.addEventListener("touchstart", (e) => {
            touchStartX = e.touches[0].clientX;
            touchStartY = e.touches[0].clientY;
        }, { passive: true });

        document.addEventListener("touchend", (e) => {
            const dx = e.changedTouches[0].clientX - touchStartX;
            const dy = e.changedTouches[0].clientY - touchStartY;

            if (Math.abs(dx) > 50 && Math.abs(dx) > Math.abs(dy)) {
                if (dx < 0) goNext();
                else goPrev();
            }
        });
    })();

    // ── 鼠标 / 触摸移动 → 唤醒按钮 ──
    document.addEventListener("mousemove", resetIdle);
    document.addEventListener("touchstart", resetIdle);

    // ── 初始化 ──
    function init() {
        if (total === 0) {
            counter.textContent = "无幻灯片";
            return;
        }

        // 从 URL hash 读取起始页
        const hash = window.location.hash.replace("#", "");
        const start = parseInt(hash, 10);
        if (!isNaN(start) && start >= 1 && start <= total) {
            current = start - 1;
        }

        navigateTo(current);
    }

    init();
})();
