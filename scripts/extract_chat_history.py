#!/usr/bin/env python3
"""Extract Claude Code chat history and convert to Markdown."""

import json
import os
from datetime import datetime
from pathlib import Path

PROJECT_DIR = Path.home() / ".claude/projects/-home-tobiasosborne-Projects-alethfeld"
OUTPUT_FILE = Path.home() / "Projects/alethfeld/chathistory.md"

def extract_text_from_content(content):
    """Extract readable text from assistant message content."""
    if isinstance(content, str):
        return content

    texts = []
    for block in content:
        if isinstance(block, dict):
            if block.get("type") == "text":
                texts.append(block.get("text", ""))
            elif block.get("type") == "tool_use":
                tool_name = block.get("name", "unknown")
                tool_input = block.get("input", {})
                # Summarize tool calls
                if tool_name == "Read":
                    texts.append(f"*[Reading file: {tool_input.get('file_path', 'unknown')}]*")
                elif tool_name == "Write":
                    texts.append(f"*[Writing file: {tool_input.get('file_path', 'unknown')}]*")
                elif tool_name == "Edit":
                    texts.append(f"*[Editing file: {tool_input.get('file_path', 'unknown')}]*")
                elif tool_name == "Bash":
                    cmd = tool_input.get("command", "")[:100]
                    texts.append(f"*[Running: `{cmd}`]*")
                elif tool_name == "Grep":
                    texts.append(f"*[Searching for: {tool_input.get('pattern', '')}]*")
                elif tool_name == "Glob":
                    texts.append(f"*[Finding files: {tool_input.get('pattern', '')}]*")
                else:
                    texts.append(f"*[Tool: {tool_name}]*")
    return "\n".join(texts)

def parse_session(filepath):
    """Parse a session JSONL file and return messages."""
    messages = []
    session_id = filepath.stem

    with open(filepath, 'r') as f:
        for line in f:
            try:
                entry = json.loads(line.strip())
                msg_type = entry.get("type")

                if msg_type == "user":
                    content = entry.get("message", {}).get("content", "")
                    timestamp = entry.get("timestamp", "")
                    messages.append({
                        "role": "user",
                        "content": content if isinstance(content, str) else str(content),
                        "timestamp": timestamp,
                        "session_id": session_id
                    })
                elif msg_type == "assistant":
                    content = entry.get("message", {}).get("content", [])
                    timestamp = entry.get("timestamp", "")
                    text = extract_text_from_content(content)
                    if text.strip():  # Only add if there's actual text
                        messages.append({
                            "role": "assistant",
                            "content": text,
                            "timestamp": timestamp,
                            "session_id": session_id
                        })
            except json.JSONDecodeError:
                continue

    return messages

def format_timestamp(ts):
    """Format ISO timestamp to readable date."""
    try:
        dt = datetime.fromisoformat(ts.replace("Z", "+00:00"))
        return dt.strftime("%Y-%m-%d %H:%M")
    except:
        return ts

def main():
    all_sessions = []

    # Find all session files
    session_files = sorted(PROJECT_DIR.glob("*.jsonl"))
    print(f"Found {len(session_files)} session files")

    for sf in session_files:
        messages = parse_session(sf)
        if messages:
            # Get first timestamp for sorting
            first_ts = messages[0].get("timestamp", "")
            all_sessions.append({
                "file": sf.name,
                "messages": messages,
                "start_time": first_ts
            })

    # Sort sessions by start time
    all_sessions.sort(key=lambda x: x["start_time"])

    # Generate markdown
    with open(OUTPUT_FILE, 'w') as out:
        out.write("# Alethfeld Project - Chat History\n\n")
        out.write(f"*Extracted from {len(all_sessions)} Claude Code sessions*\n\n")
        out.write("---\n\n")

        for i, session in enumerate(all_sessions, 1):
            session_id = session["file"].replace(".jsonl", "")[:8]
            start = format_timestamp(session["start_time"])
            out.write(f"## Session {i} ({start})\n\n")
            out.write(f"*Session ID: {session_id}...*\n\n")

            for msg in session["messages"]:
                role = msg["role"]
                content = msg["content"]

                if role == "user":
                    out.write(f"### User\n\n{content}\n\n")
                else:
                    out.write(f"### Assistant\n\n{content}\n\n")

            out.write("---\n\n")

    print(f"Chat history written to: {OUTPUT_FILE}")
    print(f"Total messages extracted: {sum(len(s['messages']) for s in all_sessions)}")

if __name__ == "__main__":
    main()
