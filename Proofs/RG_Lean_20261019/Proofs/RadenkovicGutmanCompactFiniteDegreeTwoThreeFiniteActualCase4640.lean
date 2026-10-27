/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4640 : Family 10 := level10.get ⟨716,by decide⟩
def sourceMap4640 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4640 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4640_checked : acceptsGraphIso
    (source (graph core4640) (root 10) 2 2) DegreeTwoThreeSpectrum7375.graph sourceMap4640=true := by decide +kernel
theorem fusedMap4640_checked : acceptsGraphIso
    (fused (graph core4640) (root 10) 2 2) DegreeTwoThreeSpectrum5462.graph fusedMap4640=true := by decide +kernel
theorem certified4640 : Certified (graph core4640) (root 10) 2 2 :=
  of_native_maps core4640 DegreeTwoThreeSpectrum7375.graph DegreeTwoThreeSpectrum5462.graph
    sourceMap4640 fusedMap4640 sourceMap4640_checked fusedMap4640_checked
    DegreeTwoThreeFiniteComparisons.comparison4640
#print axioms sourceMap4640_checked
#print axioms fusedMap4640_checked
#print axioms certified4640
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
