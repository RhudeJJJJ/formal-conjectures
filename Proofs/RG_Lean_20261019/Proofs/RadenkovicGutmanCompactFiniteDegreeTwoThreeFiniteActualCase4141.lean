/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4141 : Family 8 := level8.get ⟨147,by decide⟩
def sourceMap4141 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4141 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4141_checked : acceptsGraphIso
    (source (graph core4141) (root 8) 2 2) DegreeTwoThreeSpectrum3516.graph sourceMap4141=true := by decide +kernel
theorem fusedMap4141_checked : acceptsGraphIso
    (fused (graph core4141) (root 8) 2 2) DegreeTwoThreeSpectrum2717.graph fusedMap4141=true := by decide +kernel
theorem certified4141 : Certified (graph core4141) (root 8) 2 2 :=
  of_native_maps core4141 DegreeTwoThreeSpectrum3516.graph DegreeTwoThreeSpectrum2717.graph
    sourceMap4141 fusedMap4141 sourceMap4141_checked fusedMap4141_checked
    DegreeTwoThreeFiniteComparisons.comparison4141
#print axioms sourceMap4141_checked
#print axioms fusedMap4141_checked
#print axioms certified4141
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
