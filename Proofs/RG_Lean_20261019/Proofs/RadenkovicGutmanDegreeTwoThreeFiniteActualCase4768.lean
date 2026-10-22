/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4768 : Family 10 := level10.get ⟨1051,by decide⟩
def sourceMap4768 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4768 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4768_checked : acceptsGraphIso
    (source (graph core4768) (root 10) 2 2) DegreeTwoThreeSpectrum7128.graph sourceMap4768=true := by decide +kernel
theorem fusedMap4768_checked : acceptsGraphIso
    (fused (graph core4768) (root 10) 2 2) DegreeTwoThreeSpectrum6087.graph fusedMap4768=true := by decide +kernel
theorem certified4768 : Certified (graph core4768) (root 10) 2 2 :=
  of_native_maps core4768 DegreeTwoThreeSpectrum7128.graph DegreeTwoThreeSpectrum6087.graph
    sourceMap4768 fusedMap4768 sourceMap4768_checked fusedMap4768_checked
    DegreeTwoThreeFiniteComparisons.comparison4768
#print axioms sourceMap4768_checked
#print axioms fusedMap4768_checked
#print axioms certified4768
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
