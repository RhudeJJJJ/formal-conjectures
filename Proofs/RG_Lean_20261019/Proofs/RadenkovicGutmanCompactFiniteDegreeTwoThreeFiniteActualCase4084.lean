/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4084 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap4084 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,12,13,6,7,8,9,10,11] (sourceLabel 7 2 2 v)
def fusedMap4084 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4084_checked : acceptsGraphIso
    (source (graph core4084) (root 7) 2 2) DegreeTwoThreeSpectrum2279.graph sourceMap4084=true := by decide +kernel
theorem fusedMap4084_checked : acceptsGraphIso
    (fused (graph core4084) (root 7) 2 2) DegreeTwoThreeSpectrum1765.graph fusedMap4084=true := by decide +kernel
theorem certified4084 : Certified (graph core4084) (root 7) 2 2 :=
  of_native_maps core4084 DegreeTwoThreeSpectrum2279.graph DegreeTwoThreeSpectrum1765.graph
    sourceMap4084 fusedMap4084 sourceMap4084_checked fusedMap4084_checked
    DegreeTwoThreeFiniteComparisons.comparison4084
#print axioms sourceMap4084_checked
#print axioms fusedMap4084_checked
#print axioms certified4084
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
