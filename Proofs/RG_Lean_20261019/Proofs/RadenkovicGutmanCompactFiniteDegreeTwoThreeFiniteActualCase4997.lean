/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4997 : Family 10 := level10.get ⟨1616,by decide⟩
def sourceMap4997 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4997 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4997_checked : acceptsGraphIso
    (source (graph core4997) (root 10) 2 2) DegreeTwoThreeSpectrum7598.graph sourceMap4997=true := by decide +kernel
theorem fusedMap4997_checked : acceptsGraphIso
    (fused (graph core4997) (root 10) 2 2) DegreeTwoThreeSpectrum6172.graph fusedMap4997=true := by decide +kernel
theorem certified4997 : Certified (graph core4997) (root 10) 2 2 :=
  of_native_maps core4997 DegreeTwoThreeSpectrum7598.graph DegreeTwoThreeSpectrum6172.graph
    sourceMap4997 fusedMap4997 sourceMap4997_checked fusedMap4997_checked
    DegreeTwoThreeFiniteComparisons.comparison4997
#print axioms sourceMap4997_checked
#print axioms fusedMap4997_checked
#print axioms certified4997
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
