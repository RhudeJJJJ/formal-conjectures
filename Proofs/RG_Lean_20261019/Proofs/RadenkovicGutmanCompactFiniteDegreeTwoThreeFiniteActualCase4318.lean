/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4318 : Family 9 := level9.get ⟨400,by decide⟩
def sourceMap4318 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4318 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4318_checked : acceptsGraphIso
    (source (graph core4318) (root 9) 2 2) DegreeTwoThreeSpectrum4775.graph sourceMap4318=true := by decide +kernel
theorem fusedMap4318_checked : acceptsGraphIso
    (fused (graph core4318) (root 9) 2 2) DegreeTwoThreeSpectrum4356.graph fusedMap4318=true := by decide +kernel
theorem certified4318 : Certified (graph core4318) (root 9) 2 2 :=
  of_native_maps core4318 DegreeTwoThreeSpectrum4775.graph DegreeTwoThreeSpectrum4356.graph
    sourceMap4318 fusedMap4318 sourceMap4318_checked fusedMap4318_checked
    DegreeTwoThreeFiniteComparisons.comparison4318
#print axioms sourceMap4318_checked
#print axioms fusedMap4318_checked
#print axioms certified4318
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
