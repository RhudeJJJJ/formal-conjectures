/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4491 : Family 10 := level10.get ⟨257,by decide⟩
def sourceMap4491 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4491 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4491_checked : acceptsGraphIso
    (source (graph core4491) (root 10) 2 2) DegreeTwoThreeSpectrum6413.graph sourceMap4491=true := by decide +kernel
theorem fusedMap4491_checked : acceptsGraphIso
    (fused (graph core4491) (root 10) 2 2) DegreeTwoThreeSpectrum5360.graph fusedMap4491=true := by decide +kernel
theorem certified4491 : Certified (graph core4491) (root 10) 2 2 :=
  of_native_maps core4491 DegreeTwoThreeSpectrum6413.graph DegreeTwoThreeSpectrum5360.graph
    sourceMap4491 fusedMap4491 sourceMap4491_checked fusedMap4491_checked
    DegreeTwoThreeFiniteComparisons.comparison4491
#print axioms sourceMap4491_checked
#print axioms fusedMap4491_checked
#print axioms certified4491
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
