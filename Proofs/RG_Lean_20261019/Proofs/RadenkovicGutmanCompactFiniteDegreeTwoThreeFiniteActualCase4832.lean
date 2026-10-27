/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4832 : Family 10 := level10.get ⟨1208,by decide⟩
def sourceMap4832 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4832 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4832_checked : acceptsGraphIso
    (source (graph core4832) (root 10) 2 2) DegreeTwoThreeSpectrum7294.graph sourceMap4832=true := by decide +kernel
theorem fusedMap4832_checked : acceptsGraphIso
    (fused (graph core4832) (root 10) 2 2) DegreeTwoThreeSpectrum6391.graph fusedMap4832=true := by decide +kernel
theorem certified4832 : Certified (graph core4832) (root 10) 2 2 :=
  of_native_maps core4832 DegreeTwoThreeSpectrum7294.graph DegreeTwoThreeSpectrum6391.graph
    sourceMap4832 fusedMap4832 sourceMap4832_checked fusedMap4832_checked
    DegreeTwoThreeFiniteComparisons.comparison4832
#print axioms sourceMap4832_checked
#print axioms fusedMap4832_checked
#print axioms certified4832
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
