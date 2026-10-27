/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4453 : Family 10 := level10.get ⟨116,by decide⟩
def sourceMap4453 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4453 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4453_checked : acceptsGraphIso
    (source (graph core4453) (root 10) 2 2) DegreeTwoThreeSpectrum6787.graph sourceMap4453=true := by decide +kernel
theorem fusedMap4453_checked : acceptsGraphIso
    (fused (graph core4453) (root 10) 2 2) DegreeTwoThreeSpectrum5041.graph fusedMap4453=true := by decide +kernel
theorem certified4453 : Certified (graph core4453) (root 10) 2 2 :=
  of_native_maps core4453 DegreeTwoThreeSpectrum6787.graph DegreeTwoThreeSpectrum5041.graph
    sourceMap4453 fusedMap4453 sourceMap4453_checked fusedMap4453_checked
    DegreeTwoThreeFiniteComparisons.comparison4453
#print axioms sourceMap4453_checked
#print axioms fusedMap4453_checked
#print axioms certified4453
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
