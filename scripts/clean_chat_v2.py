#!/usr/bin/env python3
"""Aggressively clean chat history - conversation only."""

import re
from pathlib import Path

INPUT_FILE = Path.home() / "Projects/alethfeld/chathistory.md"
OUTPUT_FILE = Path.home() / "Projects/alethfeld/chathistory-clean.md"

def clean_content(text):
    """Remove all tool-related content, keep only conversation."""

    # Remove all XML-style tags and their contents (greedy for nested)
    # This catches function_calls, invoke, parameter, thinking, etc.
    text = re.sub(r'<[a-zA-Z_:][^>]*>.*?</[a-zA-Z_:][^>]*>', '', text, flags=re.DOTALL)

    # Remove any remaining unclosed XML-like tags to end of line
    text = re.sub(r'<[a-zA-Z_:][^>]*>.*', '', text)

    # Remove tool result markers
    text = re.sub(r'\*\[(?:Reading|Writing|Editing|Running|Searching|Finding|Tool|tool|json)[^\]]*\]\*', '', text)

    # Remove code blocks that look like JSON (start with { or [)
    text = re.sub(r'```(?:json)?\n\s*[\[{].*?```', '', text, flags=re.DOTALL)

    # Remove code blocks containing file paths or EDN
    text = re.sub(r'```(?:clojure|edn|bash|python|lean)?\n.*?```', '', text, flags=re.DOTALL)

    # Remove lines that are tool results (start with [{ for JSON arrays)
    text = re.sub(r"^\[\{'tool_use_id.*$", '', text, flags=re.MULTILINE)

    # Remove lines with numbered file content (from Read tool: "   123→content")
    text = re.sub(r'^\s*\d+→.*$', '', text, flags=re.MULTILINE)

    # Remove standalone JSON objects
    lines = text.split('\n')
    cleaned = []
    skip_until_close = 0

    for line in lines:
        stripped = line.strip()

        # Track brace depth for multi-line JSON
        if skip_until_close > 0:
            skip_until_close += stripped.count('{') - stripped.count('}')
            skip_until_close += stripped.count('[') - stripped.count(']')
            continue

        # Start of JSON object/array
        if stripped.startswith('{') or stripped.startswith('['):
            opens = stripped.count('{') + stripped.count('[')
            closes = stripped.count('}') + stripped.count(']')
            if opens > closes:
                skip_until_close = opens - closes
                continue
            elif len(stripped) > 30:  # Single-line JSON
                continue

        # Skip bare JSON-like lines
        if stripped in ['[', ']', '{', '}', '},', '],', '};']:
            continue
        if re.match(r'^"[^"]+"\s*:\s*', stripped):  # JSON key-value
            continue

        cleaned.append(line)

    text = '\n'.join(cleaned)

    # Remove excessive whitespace
    text = re.sub(r'\n{3,}', '\n\n', text)

    # Remove empty sections
    text = re.sub(r'### Assistant\n\n+(?=###|---|$)', '', text)
    text = re.sub(r'### User\n\n+(?=###|---|$)', '', text)

    return text

def main():
    print(f"Reading: {INPUT_FILE}")
    content = INPUT_FILE.read_text()
    print(f"Original: {len(content):,} chars")

    cleaned = clean_content(content)
    print(f"Cleaned: {len(cleaned):,} chars ({100*len(cleaned)//len(content)}%)")

    OUTPUT_FILE.write_text(cleaned)
    print(f"Written: {OUTPUT_FILE}")

if __name__ == "__main__":
    main()
