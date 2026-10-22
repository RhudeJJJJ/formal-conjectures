/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4831 : Family 10 := level10.get ⟨1206,by decide⟩
def sourceMap4831 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4831 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4831_checked : acceptsGraphIso
    (source (graph core4831) (root 10) 2 2) DegreeTwoThreeSpectrum7292.graph sourceMap4831=true := by decide +kernel
theorem fusedMap4831_checked : acceptsGraphIso
    (fused (graph core4831) (root 10) 2 2) DegreeTwoThreeSpectrum6387.graph fusedMap4831=true := by decide +kernel
theorem certified4831 : Certified (graph core4831) (root 10) 2 2 :=
  of_native_maps core4831 DegreeTwoThreeSpectrum7292.graph DegreeTwoThreeSpectrum6387.graph
    sourceMap4831 fusedMap4831 sourceMap4831_checked fusedMap4831_checked
    DegreeTwoThreeFiniteComparisons.comparison4831
#print axioms sourceMap4831_checked
#print axioms fusedMap4831_checked
#print axioms certified4831
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
