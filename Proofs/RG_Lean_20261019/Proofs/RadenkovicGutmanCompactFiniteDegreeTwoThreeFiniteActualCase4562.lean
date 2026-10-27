/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4562 : Family 10 := level10.get ⟨482,by decide⟩
def sourceMap4562 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,10,11,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4562 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4562_checked : acceptsGraphIso
    (source (graph core4562) (root 10) 2 2) DegreeTwoThreeSpectrum6805.graph sourceMap4562=true := by decide +kernel
theorem fusedMap4562_checked : acceptsGraphIso
    (fused (graph core4562) (root 10) 2 2) DegreeTwoThreeSpectrum5948.graph fusedMap4562=true := by decide +kernel
theorem certified4562 : Certified (graph core4562) (root 10) 2 2 :=
  of_native_maps core4562 DegreeTwoThreeSpectrum6805.graph DegreeTwoThreeSpectrum5948.graph
    sourceMap4562 fusedMap4562 sourceMap4562_checked fusedMap4562_checked
    DegreeTwoThreeFiniteComparisons.comparison4562
#print axioms sourceMap4562_checked
#print axioms fusedMap4562_checked
#print axioms certified4562
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
