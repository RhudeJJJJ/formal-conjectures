/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4895 : Family 10 := level10.get ⟨1361,by decide⟩
def sourceMap4895 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4895 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4895_checked : acceptsGraphIso
    (source (graph core4895) (root 10) 2 2) DegreeTwoThreeSpectrum7441.graph sourceMap4895=true := by decide +kernel
theorem fusedMap4895_checked : acceptsGraphIso
    (fused (graph core4895) (root 10) 2 2) DegreeTwoThreeSpectrum6698.graph fusedMap4895=true := by decide +kernel
theorem certified4895 : Certified (graph core4895) (root 10) 2 2 :=
  of_native_maps core4895 DegreeTwoThreeSpectrum7441.graph DegreeTwoThreeSpectrum6698.graph
    sourceMap4895 fusedMap4895 sourceMap4895_checked fusedMap4895_checked
    DegreeTwoThreeFiniteComparisons.comparison4895
#print axioms sourceMap4895_checked
#print axioms fusedMap4895_checked
#print axioms certified4895
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
