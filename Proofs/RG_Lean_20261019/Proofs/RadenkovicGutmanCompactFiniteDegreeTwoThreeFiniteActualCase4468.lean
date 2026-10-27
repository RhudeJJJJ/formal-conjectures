/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4468 : Family 10 := level10.get ⟨174,by decide⟩
def sourceMap4468 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,10,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4468 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4468_checked : acceptsGraphIso
    (source (graph core4468) (root 10) 2 2) DegreeTwoThreeSpectrum6836.graph sourceMap4468=true := by decide +kernel
theorem fusedMap4468_checked : acceptsGraphIso
    (fused (graph core4468) (root 10) 2 2) DegreeTwoThreeSpectrum5118.graph fusedMap4468=true := by decide +kernel
theorem certified4468 : Certified (graph core4468) (root 10) 2 2 :=
  of_native_maps core4468 DegreeTwoThreeSpectrum6836.graph DegreeTwoThreeSpectrum5118.graph
    sourceMap4468 fusedMap4468 sourceMap4468_checked fusedMap4468_checked
    DegreeTwoThreeFiniteComparisons.comparison4468
#print axioms sourceMap4468_checked
#print axioms fusedMap4468_checked
#print axioms certified4468
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
