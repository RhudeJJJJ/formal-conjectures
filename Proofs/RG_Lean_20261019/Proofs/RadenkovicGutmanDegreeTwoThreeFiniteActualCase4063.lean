/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4063 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap4063 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,8,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap4063 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4063_checked : acceptsGraphIso
    (source (graph core4063) (root 7) 2 2) DegreeTwoThreeSpectrum2185.graph sourceMap4063=true := by decide +kernel
theorem fusedMap4063_checked : acceptsGraphIso
    (fused (graph core4063) (root 7) 2 2) DegreeTwoThreeSpectrum1726.graph fusedMap4063=true := by decide +kernel
theorem certified4063 : Certified (graph core4063) (root 7) 2 2 :=
  of_native_maps core4063 DegreeTwoThreeSpectrum2185.graph DegreeTwoThreeSpectrum1726.graph
    sourceMap4063 fusedMap4063 sourceMap4063_checked fusedMap4063_checked
    DegreeTwoThreeFiniteComparisons.comparison4063
#print axioms sourceMap4063_checked
#print axioms fusedMap4063_checked
#print axioms certified4063
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
