# Carriage Features To-Do List

## My List of Features Needed

1. Add support for **footnotes**.
2. Add support for **table titles** in the placeholders.
3. Add support for **switching files** within the same working directory as the
current file, and therefore support for project folders.
4. Add support for **selecting individual section headers** from the list in the
   status bar. This will allow easier navigation between sections outside of the
   current support for navigating to previous/next sections.
5. I need to add support for the **system clipboard**.
6. When selecting text using the Shift key, I should be able to use the left
   arrow to back up to the end of the previous line with the selection.
7. Should I add support for **find and replace?** TBD.
8. When saving a new file, the program should look for the top-level header,
   strip the ATX characters, and suggest it as the filename plus a ".md"
   extension.

## From the ChatGPT Audit

After the fixes through v1.10:

1. **Table Undo/Redo is still separate from prose Undo/Redo: Medium.** Saving a
   table edit updates state.tables, but Ctrl+Z/Ctrl+R operate on the main text
   buffer. A proper fix requires document-level snapshots that include text,
   table state, and cursor position.
2. **Atomic Save can still lose inode-specific metadata: Medium/Low.** Carriage
   replaces the original file with a new inode. Permissions are preserved, but
   hard links, extended attributes, ACLs, and similar metadata may not survive.
3. **CRLF files are normalized to LF after editing: Low/Medium.** Carriage
   deliberately normalizes line endings on read and writes LF on save. This can
   create a whole-file Git diff for a Windows-formatted document even after a
   small edit.
4. **Normal Save does not fsync the containing directory: Low.** The temporary
   file itself is fsynced before os.replace(), but the destination directory is
   not. Recovery files already use the stronger pattern, so this is
   straightforward hardening.
5. **External-change detection fingerprints bytes, not file identity: Low.** A
   different inode containing exactly the same bytes counts as unchanged. Adding
   device/inode information to the snapshot would make replacement detection
   more complete.
6. **Recovery ownership relies mainly on PID liveness: Low.** A stale recovery
   could theoretically be hidden if an unrelated process later receives the same
   PID. A process-start or boot/session identifier would make recovery ownership
   more robust.
7. **Whole-document operations may become expensive on very large manuscripts:
   Low.** Word counting, table materialization, heading scans, recovery
   serialization, and file hashing can all touch the whole document. This is
   currently a performance concern rather than a correctness bug.
