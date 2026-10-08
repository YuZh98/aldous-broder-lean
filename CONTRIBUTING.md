# Contributing

Run the [verification commands](README.md#verify) before submitting changes.
Update the formalization reference when theorem statements or coverage change.

## Writing

- Keep the README focused on results, verification, and navigation.
- Put detailed hypotheses and scope qualifications in the reference page.
- Use short headings, direct sentences, and lists for parallel points.
- Preserve mathematical conditions; remove repetition and session history.

## Commits and releases

- Use an imperative commit title of at most 72 characters.
  Example: `State nonnegativity in the order law`.
- Add a body only when the reason or validation needs explanation.
- Keep release notes to a few bullets describing results and changes.
- Link to verification and scope instead of repeating them.
- At release, label the change notes and update `CITATION.cff` to match
  the tag and date. Preserve existing published tags.
