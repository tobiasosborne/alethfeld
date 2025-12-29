#!/usr/bin/env python3
"""Final pass to remove leftover XML fragments."""

import re
from pathlib import Path

INPUT_FILE = Path.home() / "Projects/alethfeld/chathistory-clean.md"
OUTPUT_FILE = Path.home() / "Projects/alethfeld/chathistory-clean.md"

def clean_fragments(text):
    """Remove leftover XML fragments and noise."""

    # Remove closing tags that got orphaned
    text = re.sub(r'</[a-zA-Z_:]+>', '', text)

    # Remove opening tags that got orphaned  
    text = re.sub(r'<[a-zA-Z_:][a-zA-Z_:0-9]*[^>]*>', '', text)

    # Remove lines that are just whitespace or very short fragments
    lines = text.split('\n')
    cleaned = []
    for line in lines:
        stripped = line.strip()
        # Skip empty lines that aren't paragraph breaks
        if not stripped:
            cleaned.append(line)
            continue
        # Skip very short noise lines
        if len(stripped) < 3 and stripped not in ['#', '-', '*']:
            continue
        cleaned.append(line)

    text = '\n'.join(cleaned)

    # Clean up multiple blank lines
    text = re.sub(r'\n{3,}', '\n\n', text)

    # Remove empty assistant/user blocks
    text = re.sub(r'### Assistant\n\n(?=###|---|\n*$)', '', text)
    text = re.sub(r'### User\n\n(?=###|---|\n*$)', '', text)

    return text

def main():
    content = INPUT_FILE.read_text()
    print(f"Before: {len(content):,} chars")

    cleaned = clean_fragments(content)
    print(f"After: {len(cleaned):,} chars")

    OUTPUT_FILE.write_text(cleaned)
    print(f"Written: {OUTPUT_FILE}")

if __name__ == "__main__":
    main()
