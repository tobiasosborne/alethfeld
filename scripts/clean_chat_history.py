#!/usr/bin/env python3
"""Clean chat history by removing tool use blocks and JSON."""

import re
from pathlib import Path

INPUT_FILE = Path.home() / "Projects/alethfeld/chathistory.md"
OUTPUT_FILE = Path.home() / "Projects/alethfeld/chathistory-clean.md"

def clean_content(text):
    """Remove tool calls, JSON blocks, and other noise."""

    # Remove XML-style function/invoke/parameter blocks (multi-line)
    # Using raw tag names to avoid any issues
    for tag in ['function_calls', 'invoke', 'parameter', 'thinking', 'antml:function_calls', 'antml:invoke', 'antml:parameter', 'antml:thinking']:
        pattern = f'<{tag}[^>]*>.*?</{tag}>'
        text = re.sub(pattern, '', text, flags=re.DOTALL | re.IGNORECASE)

    # Remove any remaining unclosed XML-like tags related to tools
    text = re.sub(r'<(function_calls|invoke|parameter|thinking|antml:[a-z_]+)[^>]*>.*', '', text, flags=re.IGNORECASE)

    # Remove lines that are just tool use markers we added
    text = re.sub(r'\*\[(?:Reading|Writing|Editing|Running|Searching|Finding|Tool)[^\]]*\]\*\n?', '', text)

    # Remove JSON-like content in code blocks that starts with {
    text = re.sub(r'```json\n\{.*?\n```', '*[json removed]*', text, flags=re.DOTALL)
    text = re.sub(r'```\n\{.*?\n```', '*[json removed]*', text, flags=re.DOTALL)

    # Remove standalone JSON objects (lines starting with { and multi-line)
    # Be careful to only remove obvious JSON, not code examples
    lines = text.split('\n')
    cleaned_lines = []
    in_json_block = False
    brace_count = 0

    for line in lines:
        stripped = line.strip()

        # Detect start of JSON block
        if stripped.startswith('{') and not in_json_block:
            brace_count = stripped.count('{') - stripped.count('}')
            if brace_count > 0:
                in_json_block = True
                continue
            elif brace_count == 0 and len(stripped) > 50:
                # Single-line JSON, skip it
                continue

        # Continue skipping JSON
        if in_json_block:
            brace_count += stripped.count('{') - stripped.count('}')
            if brace_count <= 0:
                in_json_block = False
            continue

        # Skip lines that look like raw JSON array/object continuations
        if stripped.startswith('"') and stripped.endswith(','):
            continue
        if stripped in ['[', ']', '{', '}', '},', '],']:
            continue

        cleaned_lines.append(line)

    text = '\n'.join(cleaned_lines)

    # Remove multiple consecutive blank lines
    text = re.sub(r'\n{4,}', '\n\n\n', text)

    # Remove empty assistant sections
    text = re.sub(r'### Assistant\n\n+(?=###|---|$)', '', text)

    return text

def main():
    print(f"Reading: {INPUT_FILE}")
    with open(INPUT_FILE, 'r') as f:
        content = f.read()

    print(f"Original size: {len(content):,} chars")

    cleaned = clean_content(content)

    print(f"Cleaned size: {len(cleaned):,} chars")

    with open(OUTPUT_FILE, 'w') as f:
        f.write(cleaned)

    print(f"Written to: {OUTPUT_FILE}")

if __name__ == "__main__":
    main()
