/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4089 : Family 7 := level7.get ⟨87,by decide⟩
def sourceMap4089 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4089 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4089_checked : acceptsGraphIso
    (source (graph core4089) (root 7) 2 2) DegreeTwoThreeSpectrum2297.graph sourceMap4089=true := by decide +kernel
theorem fusedMap4089_checked : acceptsGraphIso
    (fused (graph core4089) (root 7) 2 2) DegreeTwoThreeSpectrum1818.graph fusedMap4089=true := by decide +kernel
theorem certified4089 : Certified (graph core4089) (root 7) 2 2 :=
  of_native_maps core4089 DegreeTwoThreeSpectrum2297.graph DegreeTwoThreeSpectrum1818.graph
    sourceMap4089 fusedMap4089 sourceMap4089_checked fusedMap4089_checked
    DegreeTwoThreeFiniteComparisons.comparison4089
#print axioms sourceMap4089_checked
#print axioms fusedMap4089_checked
#print axioms certified4089
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
