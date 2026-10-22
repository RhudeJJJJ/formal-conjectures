/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4519 : Family 10 := level10.get ⟨353,by decide⟩
def sourceMap4519 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4519 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4519_checked : acceptsGraphIso
    (source (graph core4519) (root 10) 2 2) DegreeTwoThreeSpectrum6776.graph sourceMap4519=true := by decide +kernel
theorem fusedMap4519_checked : acceptsGraphIso
    (fused (graph core4519) (root 10) 2 2) DegreeTwoThreeSpectrum5628.graph fusedMap4519=true := by decide +kernel
theorem certified4519 : Certified (graph core4519) (root 10) 2 2 :=
  of_native_maps core4519 DegreeTwoThreeSpectrum6776.graph DegreeTwoThreeSpectrum5628.graph
    sourceMap4519 fusedMap4519 sourceMap4519_checked fusedMap4519_checked
    DegreeTwoThreeFiniteComparisons.comparison4519
#print axioms sourceMap4519_checked
#print axioms fusedMap4519_checked
#print axioms certified4519
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
