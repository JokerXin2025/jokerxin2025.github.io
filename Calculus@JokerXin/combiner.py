import os
import re

def process_lean_code(filepath):
    """提取 Lean 代码：去除证明部分，剔除 import 语句及特定 option"""
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    result = []
    in_proof = False
    decl_indent = 0
    
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        lstripped = line.lstrip()
        current_indent = len(line) - len(lstripped)

        # 需求 1 & 2：彻底去除文件内的所有 import 语句 和 指定的 linter option
        # 注意：Lean 的 import 必须顶格写，所以用 line.startswith 更安全，避免删掉注释里的词
        if line.startswith("import "):
            i += 1
            continue
            
        if stripped == "set_option linter.style.header false":
            i += 1
            continue

        if not lstripped:
            if not in_proof: result.append(line)
            i += 1
            continue

        if in_proof:
            if current_indent > decl_indent:
                i += 1
                continue
            else:
                in_proof = False

        if not in_proof:
            if lstripped.startswith("theorem ") or lstripped.startswith("lemma ") or lstripped.startswith("example "):
                decl_indent = current_indent
                decl_lines = []
                while i < len(lines):
                    sub_line = lines[i]
                    if ":=" in sub_line:
                        part_before = sub_line.split(":=")[0]
                        decl_lines.append(part_before + ":= sorry\n")
                        in_proof = True
                        break
                    else:
                        decl_lines.append(sub_line)
                    i += 1
                
                result.extend(decl_lines)
                i += 1
                continue
                
            result.append(line)
            
        i += 1

    return "".join(result)

def parse_imports(filepath):
    """安全解析并返回: [(标准化模块名, 原始代码行), ...]"""
    imports = []
    import_pattern = re.compile(r'^import\s+([A-Za-z0-9_.«»]+)')
    
    if not os.path.exists(filepath):
        return imports
        
    in_comment = False
    with open(filepath, 'r', encoding='utf-8') as f:
        for line in f:
            stripped = line.strip()
            
            # 处理多行注释块 (简化版，足够应对头部注释)
            if stripped.startswith('/-') and '-/' not in stripped:
                in_comment = True
                continue
            if in_comment:
                if '-/' in stripped:
                    in_comment = False
                continue
                
            # 过滤单行注释
            if stripped.startswith('--'):
                continue
                
            match = import_pattern.match(stripped)
            if match:
                raw_import = match.group(1)
                normalized_import = raw_import.replace('«', '').replace('»', '')
                imports.append((normalized_import, stripped))
                
    return imports

def main():
    root_dir = os.path.abspath(".")
    project_name = "Calculus_21"  
    main_file = os.path.join(root_dir, f"{project_name}.lean")
    
    if not os.path.exists(main_file):
        print(f"❌ 找不到主文件: {main_file}")
        return

    print(f"🔍 锁定项目名称: {project_name}")
    print(f"📍 主文件入口: {main_file}")

    visited = set()
    sorted_files = []
    external_imports = set()  # 用于全局收集所有的外部 import

    def dfs(filepath):
        if filepath in visited:
            return
        visited.add(filepath)
        
        imports = parse_imports(filepath)
        for norm_imp, raw_line in imports:
            # 判断是否为内部依赖
            if norm_imp.startswith(project_name):
                # 需求 3：严格的标准化路径解析
                if norm_imp == project_name:
                    rel_path = f"{project_name}.lean"
                else:
                    rel_path = norm_imp.replace('.', os.sep) + '.lean'
                
                dep_filepath = os.path.join(root_dir, rel_path)
                
                if os.path.exists(dep_filepath):
                    dfs(dep_filepath)
                else:
                    print(f"⚠️ 警告: 找不到内部依赖文件 {rel_path} (源自 {os.path.basename(filepath)})")
            else:
                # 非项目内部的 import，归类为外部依赖 (如 Mathlib 等)
                external_imports.add(raw_line)

        # 深度优先，底层的依赖最先被加入列表
        sorted_files.append(filepath)

    print("🕸️ 正在追踪依赖树并分离外部依赖...")
    dfs(main_file)
    print(f"✅ 追踪完成，共识别出 {len(sorted_files)} 个内部文件，{len(external_imports)} 个外部依赖。")

    print("📝 正在按照正确的拓扑顺序提取代码并组装...")
    
    # 组装最终文件：先放所有的外部 import
    merged_content = ""
    if external_imports:
        merged_content += "-- === 外部依赖 (External Imports) ===\n"
        # 排序，让外部 import 看起来整齐
        for ext_imp in sorted(external_imports):
            merged_content += ext_imp + "\n"
        merged_content += "\n"

    # 再放所有的内部文件代码
    for filepath in sorted_files:
        rel_path = os.path.relpath(filepath, root_dir)
        print(f" -> 合并: {rel_path}")
        
        merged_content += f"-- ========================================== --\n"
        merged_content += f"-- File: {rel_path}\n"
        merged_content += f"-- ========================================== --\n\n"
        merged_content += process_lean_code(filepath)
        merged_content += "\n\n"

    output_file = f"{project_name}_API_sorted.lean"
    with open(output_file, "w", encoding="utf-8") as f:
        f.write(merged_content)
        
    print(f"\n🎉 大功告成！完美合并后的全局 API 字典已保存至: {output_file}")

if __name__ == "__main__":
    main()
