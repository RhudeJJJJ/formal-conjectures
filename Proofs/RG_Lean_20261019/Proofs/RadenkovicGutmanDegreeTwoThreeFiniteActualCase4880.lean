/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4880 : Family 10 := level10.get ⟨1326,by decide⟩
def sourceMap4880 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4880 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4880_checked : acceptsGraphIso
    (source (graph core4880) (root 10) 2 2) DegreeTwoThreeSpectrum7407.graph sourceMap4880=true := by decide +kernel
theorem fusedMap4880_checked : acceptsGraphIso
    (fused (graph core4880) (root 10) 2 2) DegreeTwoThreeSpectrum6636.graph fusedMap4880=true := by decide +kernel
theorem certified4880 : Certified (graph core4880) (root 10) 2 2 :=
  of_native_maps core4880 DegreeTwoThreeSpectrum7407.graph DegreeTwoThreeSpectrum6636.graph
    sourceMap4880 fusedMap4880 sourceMap4880_checked fusedMap4880_checked
    DegreeTwoThreeFiniteComparisons.comparison4880
#print axioms sourceMap4880_checked
#print axioms fusedMap4880_checked
#print axioms certified4880
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
