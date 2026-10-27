/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4356 : Family 9 := level9.get ⟨493,by decide⟩
def sourceMap4356 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,8,9,10,11,12,13,14,15,7,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4356 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4356_checked : acceptsGraphIso
    (source (graph core4356) (root 9) 2 2) DegreeTwoThreeSpectrum4884.graph sourceMap4356=true := by decide +kernel
theorem fusedMap4356_checked : acceptsGraphIso
    (fused (graph core4356) (root 9) 2 2) DegreeTwoThreeSpectrum4568.graph fusedMap4356=true := by decide +kernel
theorem certified4356 : Certified (graph core4356) (root 9) 2 2 :=
  of_native_maps core4356 DegreeTwoThreeSpectrum4884.graph DegreeTwoThreeSpectrum4568.graph
    sourceMap4356 fusedMap4356 sourceMap4356_checked fusedMap4356_checked
    DegreeTwoThreeFiniteComparisons.comparison4356
#print axioms sourceMap4356_checked
#print axioms fusedMap4356_checked
#print axioms certified4356
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
