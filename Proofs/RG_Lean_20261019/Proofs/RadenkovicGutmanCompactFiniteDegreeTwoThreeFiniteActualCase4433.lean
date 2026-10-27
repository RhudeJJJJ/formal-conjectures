/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4433 : Family 10 := level10.get ⟨17,by decide⟩
def sourceMap4433 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4433 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4433_checked : acceptsGraphIso
    (source (graph core4433) (root 10) 2 2) DegreeTwoThreeSpectrum5413.graph sourceMap4433=true := by decide +kernel
theorem fusedMap4433_checked : acceptsGraphIso
    (fused (graph core4433) (root 10) 2 2) DegreeTwoThreeSpectrum5006.graph fusedMap4433=true := by decide +kernel
theorem certified4433 : Certified (graph core4433) (root 10) 2 2 :=
  of_native_maps core4433 DegreeTwoThreeSpectrum5413.graph DegreeTwoThreeSpectrum5006.graph
    sourceMap4433 fusedMap4433 sourceMap4433_checked fusedMap4433_checked
    DegreeTwoThreeFiniteComparisons.comparison4433
#print axioms sourceMap4433_checked
#print axioms fusedMap4433_checked
#print axioms certified4433
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
