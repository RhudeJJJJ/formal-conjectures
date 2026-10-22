/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4322 : Family 9 := level9.get ⟨407,by decide⟩
def sourceMap4322 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 9 2 2 v)
def fusedMap4322 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4322_checked : acceptsGraphIso
    (source (graph core4322) (root 9) 2 2) DegreeTwoThreeSpectrum4762.graph sourceMap4322=true := by decide +kernel
theorem fusedMap4322_checked : acceptsGraphIso
    (fused (graph core4322) (root 9) 2 2) DegreeTwoThreeSpectrum4371.graph fusedMap4322=true := by decide +kernel
theorem certified4322 : Certified (graph core4322) (root 9) 2 2 :=
  of_native_maps core4322 DegreeTwoThreeSpectrum4762.graph DegreeTwoThreeSpectrum4371.graph
    sourceMap4322 fusedMap4322 sourceMap4322_checked fusedMap4322_checked
    DegreeTwoThreeFiniteComparisons.comparison4322
#print axioms sourceMap4322_checked
#print axioms fusedMap4322_checked
#print axioms certified4322
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
