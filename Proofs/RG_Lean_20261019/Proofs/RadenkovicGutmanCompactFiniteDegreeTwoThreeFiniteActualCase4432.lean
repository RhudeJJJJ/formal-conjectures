/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4432 : Family 10 := level10.get ⟨9,by decide⟩
def sourceMap4432 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,2,1,0,11,12,13,14,15,16,10,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap4432 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (fusedLabel 10 2 2 v)
theorem sourceMap4432_checked : acceptsGraphIso
    (source (graph core4432) (root 10) 2 2) DegreeTwoThreeSpectrum5661.graph sourceMap4432=true := by decide +kernel
theorem fusedMap4432_checked : acceptsGraphIso
    (fused (graph core4432) (root 10) 2 2) DegreeTwoThreeSpectrum4964.graph fusedMap4432=true := by decide +kernel
theorem certified4432 : Certified (graph core4432) (root 10) 2 2 :=
  of_native_maps core4432 DegreeTwoThreeSpectrum5661.graph DegreeTwoThreeSpectrum4964.graph
    sourceMap4432 fusedMap4432 sourceMap4432_checked fusedMap4432_checked
    DegreeTwoThreeFiniteComparisons.comparison4432
#print axioms sourceMap4432_checked
#print axioms fusedMap4432_checked
#print axioms certified4432
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
