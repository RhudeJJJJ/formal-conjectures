/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4375 : Family 9 := level9.get ⟨531,by decide⟩
def sourceMap4375 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,12,13,14,15,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 2 2 v)
def fusedMap4375 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4375_checked : acceptsGraphIso
    (source (graph core4375) (root 9) 2 2) DegreeTwoThreeSpectrum4824.graph sourceMap4375=true := by decide +kernel
theorem fusedMap4375_checked : acceptsGraphIso
    (fused (graph core4375) (root 9) 2 2) DegreeTwoThreeSpectrum4637.graph fusedMap4375=true := by decide +kernel
theorem certified4375 : Certified (graph core4375) (root 9) 2 2 :=
  of_native_maps core4375 DegreeTwoThreeSpectrum4824.graph DegreeTwoThreeSpectrum4637.graph
    sourceMap4375 fusedMap4375 sourceMap4375_checked fusedMap4375_checked
    DegreeTwoThreeFiniteComparisons.comparison4375
#print axioms sourceMap4375_checked
#print axioms fusedMap4375_checked
#print axioms certified4375
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
