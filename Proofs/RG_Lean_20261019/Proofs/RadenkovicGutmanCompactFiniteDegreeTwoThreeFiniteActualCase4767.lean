/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4767 : Family 10 := level10.get ⟨1050,by decide⟩
def sourceMap4767 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4767 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4767_checked : acceptsGraphIso
    (source (graph core4767) (root 10) 2 2) DegreeTwoThreeSpectrum7127.graph sourceMap4767=true := by decide +kernel
theorem fusedMap4767_checked : acceptsGraphIso
    (fused (graph core4767) (root 10) 2 2) DegreeTwoThreeSpectrum6085.graph fusedMap4767=true := by decide +kernel
theorem certified4767 : Certified (graph core4767) (root 10) 2 2 :=
  of_native_maps core4767 DegreeTwoThreeSpectrum7127.graph DegreeTwoThreeSpectrum6085.graph
    sourceMap4767 fusedMap4767 sourceMap4767_checked fusedMap4767_checked
    DegreeTwoThreeFiniteComparisons.comparison4767
#print axioms sourceMap4767_checked
#print axioms fusedMap4767_checked
#print axioms certified4767
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
