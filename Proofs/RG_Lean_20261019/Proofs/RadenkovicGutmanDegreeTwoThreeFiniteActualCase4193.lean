/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4193 : Family 9 := level9.get ⟨8,by decide⟩
def sourceMap4193 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,10,11,12,13,14,15,9,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap4193 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (fusedLabel 9 2 2 v)
theorem sourceMap4193_checked : acceptsGraphIso
    (source (graph core4193) (root 9) 2 2) DegreeTwoThreeSpectrum4059.graph sourceMap4193=true := by decide +kernel
theorem fusedMap4193_checked : acceptsGraphIso
    (fused (graph core4193) (root 9) 2 2) DegreeTwoThreeSpectrum3891.graph fusedMap4193=true := by decide +kernel
theorem certified4193 : Certified (graph core4193) (root 9) 2 2 :=
  of_native_maps core4193 DegreeTwoThreeSpectrum4059.graph DegreeTwoThreeSpectrum3891.graph
    sourceMap4193 fusedMap4193 sourceMap4193_checked fusedMap4193_checked
    DegreeTwoThreeFiniteComparisons.comparison4193
#print axioms sourceMap4193_checked
#print axioms fusedMap4193_checked
#print axioms certified4193
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
