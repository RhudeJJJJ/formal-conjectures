/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4094 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap4094 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap4094 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4094_checked : acceptsGraphIso
    (source (graph core4094) (root 7) 2 2) DegreeTwoThreeSpectrum2306.graph sourceMap4094=true := by decide +kernel
theorem fusedMap4094_checked : acceptsGraphIso
    (fused (graph core4094) (root 7) 2 2) DegreeTwoThreeSpectrum1928.graph fusedMap4094=true := by decide +kernel
theorem certified4094 : Certified (graph core4094) (root 7) 2 2 :=
  of_native_maps core4094 DegreeTwoThreeSpectrum2306.graph DegreeTwoThreeSpectrum1928.graph
    sourceMap4094 fusedMap4094 sourceMap4094_checked fusedMap4094_checked
    DegreeTwoThreeFiniteComparisons.comparison4094
#print axioms sourceMap4094_checked
#print axioms fusedMap4094_checked
#print axioms certified4094
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
