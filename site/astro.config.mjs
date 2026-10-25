// @ts-check
import fs from 'node:fs';
import { defineConfig } from 'astro/config';
import starlight from '@astrojs/starlight';
import { readToc, sidebarGroup } from './scripts/toc.mjs';

// Syntax highlighting for ```jihoo code blocks.
const jihoo = JSON.parse(fs.readFileSync(new URL('./src/jihoo.tmLanguage.json', import.meta.url), 'utf-8'));

// The sidebar follows the table of contents in docs/README.md; the examples come
// right after the language.
const toc = readToc().groups.map(sidebarGroup);
const examples = { label: 'Examples', items: [{ autogenerate: { directory: 'examples' } }] };
const sidebar = [
  { label: 'Start here', items: ['start/getting-started'] },
  ...toc.flatMap((g) => (g.label === 'Language' ? [g, examples] : [g])),
];

// GitHub Pages serves the site under /<repository>/. The deploy workflow passes
// the exact origin and path; these defaults match github.com/jihoolang/jihoo.
const base = process.env.BASE_PATH ?? '/jihoo';

// Pages that moved. The 0.1 rewrite replaced every page, so none redirect.
const moved = {};

export default defineConfig({
  site: process.env.SITE_URL ?? 'https://jihoolang.github.io',
  base,
  redirects: Object.fromEntries(
    Object.entries(moved).map(([from, to]) => [`/${from}`, `${base.replace(/\/$/, '')}/${to}/`]),
  ),
  integrations: [
    starlight({
      title: 'jihoo',
      description:
        'A systems language as fast as C, memory-safe without lifetimes or a garbage collector.',
      favicon: '/favicon.svg',
      social: [{ icon: 'github', label: 'GitHub', href: 'https://github.com/jihoolang/jihoo' }],
      customCss: ['./src/styles/custom.css'],
      expressiveCode: { shiki: { langs: [jihoo] } },
      sidebar,
    }),
  ],
});
