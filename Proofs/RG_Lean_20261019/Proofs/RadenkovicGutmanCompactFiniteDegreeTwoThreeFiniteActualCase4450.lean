/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4450 : Family 10 := level10.get ⟨104,by decide⟩
def sourceMap4450 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4450 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4450_checked : acceptsGraphIso
    (source (graph core4450) (root 10) 2 2) DegreeTwoThreeSpectrum6744.graph sourceMap4450=true := by decide +kernel
theorem fusedMap4450_checked : acceptsGraphIso
    (fused (graph core4450) (root 10) 2 2) DegreeTwoThreeSpectrum5026.graph fusedMap4450=true := by decide +kernel
theorem certified4450 : Certified (graph core4450) (root 10) 2 2 :=
  of_native_maps core4450 DegreeTwoThreeSpectrum6744.graph DegreeTwoThreeSpectrum5026.graph
    sourceMap4450 fusedMap4450 sourceMap4450_checked fusedMap4450_checked
    DegreeTwoThreeFiniteComparisons.comparison4450
#print axioms sourceMap4450_checked
#print axioms fusedMap4450_checked
#print axioms certified4450
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
