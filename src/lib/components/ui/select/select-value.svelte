<script lang="ts">
	/** A simple display component — renders its children or a placeholder. */
	let {
		placeholder = "",
		children,
	}: { placeholder?: string; children?: import("svelte").Snippet } = $props();
</script>

{#if children}
	{@render children()}
{:else}
	<span class="text-muted-foreground">{placeholder}</span>
{/if}
