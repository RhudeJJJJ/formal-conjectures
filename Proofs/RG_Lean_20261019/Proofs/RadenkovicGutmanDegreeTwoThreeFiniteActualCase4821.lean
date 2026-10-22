/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4821 : Family 10 := level10.get ⟨1184,by decide⟩
def sourceMap4821 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4821 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4821_checked : acceptsGraphIso
    (source (graph core4821) (root 10) 2 2) DegreeTwoThreeSpectrum7276.graph sourceMap4821=true := by decide +kernel
theorem fusedMap4821_checked : acceptsGraphIso
    (fused (graph core4821) (root 10) 2 2) DegreeTwoThreeSpectrum6353.graph fusedMap4821=true := by decide +kernel
theorem certified4821 : Certified (graph core4821) (root 10) 2 2 :=
  of_native_maps core4821 DegreeTwoThreeSpectrum7276.graph DegreeTwoThreeSpectrum6353.graph
    sourceMap4821 fusedMap4821 sourceMap4821_checked fusedMap4821_checked
    DegreeTwoThreeFiniteComparisons.comparison4821
#print axioms sourceMap4821_checked
#print axioms fusedMap4821_checked
#print axioms certified4821
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
