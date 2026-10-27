/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4840 : Family 10 := level10.get ⟨1223,by decide⟩
def sourceMap4840 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4840 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4840_checked : acceptsGraphIso
    (source (graph core4840) (root 10) 2 2) DegreeTwoThreeSpectrum7321.graph sourceMap4840=true := by decide +kernel
theorem fusedMap4840_checked : acceptsGraphIso
    (fused (graph core4840) (root 10) 2 2) DegreeTwoThreeSpectrum6423.graph fusedMap4840=true := by decide +kernel
theorem certified4840 : Certified (graph core4840) (root 10) 2 2 :=
  of_native_maps core4840 DegreeTwoThreeSpectrum7321.graph DegreeTwoThreeSpectrum6423.graph
    sourceMap4840 fusedMap4840 sourceMap4840_checked fusedMap4840_checked
    DegreeTwoThreeFiniteComparisons.comparison4840
#print axioms sourceMap4840_checked
#print axioms fusedMap4840_checked
#print axioms certified4840
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
