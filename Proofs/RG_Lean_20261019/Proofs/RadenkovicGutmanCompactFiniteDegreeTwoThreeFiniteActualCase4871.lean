/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4871 : Family 10 := level10.get ⟨1303,by decide⟩
def sourceMap4871 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4871 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4871_checked : acceptsGraphIso
    (source (graph core4871) (root 10) 2 2) DegreeTwoThreeSpectrum7384.graph sourceMap4871=true := by decide +kernel
theorem fusedMap4871_checked : acceptsGraphIso
    (fused (graph core4871) (root 10) 2 2) DegreeTwoThreeSpectrum6594.graph fusedMap4871=true := by decide +kernel
theorem certified4871 : Certified (graph core4871) (root 10) 2 2 :=
  of_native_maps core4871 DegreeTwoThreeSpectrum7384.graph DegreeTwoThreeSpectrum6594.graph
    sourceMap4871 fusedMap4871 sourceMap4871_checked fusedMap4871_checked
    DegreeTwoThreeFiniteComparisons.comparison4871
#print axioms sourceMap4871_checked
#print axioms fusedMap4871_checked
#print axioms certified4871
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
