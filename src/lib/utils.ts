import { clsx, type ClassValue } from "clsx";
import { twMerge } from "tailwind-merge";
import type { Snippet } from "svelte";

export function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

export type WithElementRef<T, U extends HTMLElement = HTMLElement> = T & {
  ref?: U | null;
};

export type WithoutChild<T> = T extends { children?: Snippet } ? Omit<T, "children"> : T;

export type WithoutChildren<T> = T extends { children?: Snippet } ? Omit<T, "children"> : T;

export type WithoutChildrenOrChild<T> = T extends { children?: Snippet; child?: Snippet }
  ? Omit<T, "children" | "child">
  : T;
