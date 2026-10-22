/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4464 : Family 10 := level10.get ⟨161,by decide⟩
def sourceMap4464 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,10,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4464 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4464_checked : acceptsGraphIso
    (source (graph core4464) (root 10) 2 2) DegreeTwoThreeSpectrum6835.graph sourceMap4464=true := by decide +kernel
theorem fusedMap4464_checked : acceptsGraphIso
    (fused (graph core4464) (root 10) 2 2) DegreeTwoThreeSpectrum5099.graph fusedMap4464=true := by decide +kernel
theorem certified4464 : Certified (graph core4464) (root 10) 2 2 :=
  of_native_maps core4464 DegreeTwoThreeSpectrum6835.graph DegreeTwoThreeSpectrum5099.graph
    sourceMap4464 fusedMap4464 sourceMap4464_checked fusedMap4464_checked
    DegreeTwoThreeFiniteComparisons.comparison4464
#print axioms sourceMap4464_checked
#print axioms fusedMap4464_checked
#print axioms certified4464
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
