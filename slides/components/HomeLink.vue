<script setup>
import { computed } from 'vue'

const props = defineProps({
  label: { type: String, default: 'Home' },
})

const home = computed(() => {
  const base = import.meta.env.BASE_URL || '/'
  return base.replace(/(?:programmers|biologists)\/$/, '') || '/'
})
</script>

<template>
  <a class="ap1-home" :href="home">{{ props.label }}</a>
</template>

<style scoped>
.ap1-home {
  position: fixed;
  right: 0.8rem;
  bottom: 0.6rem;
  z-index: 40;
  padding: 0.25rem 0.7rem;
  border-radius: 999px;
  font-size: 0.8rem;
  letter-spacing: 0.02em;
  text-decoration: none;
  color: var(--slidev-theme-primary, #3b82f6);
  background: rgba(255, 255, 255, 0.72);
  border: 1px solid currentColor;
  backdrop-filter: blur(4px);
}

.dark .ap1-home {
  background: rgba(15, 23, 42, 0.72);
}
</style>
