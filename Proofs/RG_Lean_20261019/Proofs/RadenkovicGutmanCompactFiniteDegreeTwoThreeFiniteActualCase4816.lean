/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4816 : Family 10 := level10.get ⟨1168,by decide⟩
def sourceMap4816 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4816 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4816_checked : acceptsGraphIso
    (source (graph core4816) (root 10) 2 2) DegreeTwoThreeSpectrum7250.graph sourceMap4816=true := by decide +kernel
theorem fusedMap4816_checked : acceptsGraphIso
    (fused (graph core4816) (root 10) 2 2) DegreeTwoThreeSpectrum6320.graph fusedMap4816=true := by decide +kernel
theorem certified4816 : Certified (graph core4816) (root 10) 2 2 :=
  of_native_maps core4816 DegreeTwoThreeSpectrum7250.graph DegreeTwoThreeSpectrum6320.graph
    sourceMap4816 fusedMap4816 sourceMap4816_checked fusedMap4816_checked
    DegreeTwoThreeFiniteComparisons.comparison4816
#print axioms sourceMap4816_checked
#print axioms fusedMap4816_checked
#print axioms certified4816
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
