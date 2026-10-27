/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4467 : Family 10 := level10.get ⟨171,by decide⟩
def sourceMap4467 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4467 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4467_checked : acceptsGraphIso
    (source (graph core4467) (root 10) 2 2) DegreeTwoThreeSpectrum6857.graph sourceMap4467=true := by decide +kernel
theorem fusedMap4467_checked : acceptsGraphIso
    (fused (graph core4467) (root 10) 2 2) DegreeTwoThreeSpectrum5114.graph fusedMap4467=true := by decide +kernel
theorem certified4467 : Certified (graph core4467) (root 10) 2 2 :=
  of_native_maps core4467 DegreeTwoThreeSpectrum6857.graph DegreeTwoThreeSpectrum5114.graph
    sourceMap4467 fusedMap4467 sourceMap4467_checked fusedMap4467_checked
    DegreeTwoThreeFiniteComparisons.comparison4467
#print axioms sourceMap4467_checked
#print axioms fusedMap4467_checked
#print axioms certified4467
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
