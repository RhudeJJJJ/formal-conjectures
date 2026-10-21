/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1334 : Family 9 := level9.get ⟨89,by decide⟩
def sourceMap1334 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1334 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1334_checked : acceptsGraphIso
    (source (graph core1334) (root 9) 0 1) DegreeOneSmallSpectrum1420.graph sourceMap1334=true := by decide +kernel
theorem fusedMap1334_checked : acceptsGraphIso
    (fused (graph core1334) (root 9) 0 1) DegreeOneSmallSpectrum942.graph fusedMap1334=true := by decide +kernel
theorem certified1334 : Certified (graph core1334) (root 9) 0 1 :=
  of_native_maps core1334 DegreeOneSmallSpectrum1420.graph DegreeOneSmallSpectrum942.graph
    sourceMap1334 fusedMap1334 sourceMap1334_checked fusedMap1334_checked
    DegreeOneSmallComparisons.comparison1334
#print axioms sourceMap1334_checked
#print axioms fusedMap1334_checked
#print axioms certified1334
def sourceMap1334swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1334swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1334swap_checked : acceptsGraphIso
    (source (graph core1334) (root 9) 1 0) DegreeOneSmallSpectrum1420.graph sourceMap1334swap=true := by decide +kernel
theorem fusedMap1334swap_checked : acceptsGraphIso
    (fused (graph core1334) (root 9) 1 0) DegreeOneSmallSpectrum942.graph fusedMap1334swap=true := by decide +kernel
theorem certified1334swap : Certified (graph core1334) (root 9) 1 0 :=
  of_native_maps core1334 DegreeOneSmallSpectrum1420.graph DegreeOneSmallSpectrum942.graph
    sourceMap1334swap fusedMap1334swap sourceMap1334swap_checked fusedMap1334swap_checked
    DegreeOneSmallComparisons.comparison1334
#print axioms sourceMap1334swap_checked
#print axioms fusedMap1334swap_checked
#print axioms certified1334swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
